/*!
This module contains a boat load of wrappers around each of our internal regex
engines. They encapsulate a few things:

1. The wrappers manage the conditional existence of the regex engine. Namely,
the PikeVM is the only required regex engine. The rest are optional. These
wrappers present a uniform API regardless of which engines are available. And
availability might be determined by compile time features or by dynamic
configuration via `meta::Config`. Encapsulating the conditional compilation
features is in particular a huge simplification for the higher level code that
composes these engines.
2. The wrappers manage construction of each engine, including skipping it if
the engine is unavailable or configured to not be used.
3. The wrappers manage whether an engine *can* be used for a particular
search configuration. For example, `BoundedBacktracker::get` only returns a
backtracking engine when the haystack is bigger than the maximum supported
length. The wrappers also sometimes take a position on when an engine *ought*
to be used, but only in cases where the logic is extremely local to the engine
itself. Otherwise, things like "choose between the backtracker and the one-pass
DFA" are managed by the higher level meta strategy code.

There are also corresponding wrappers for the various `Cache` types for each
regex engine that needs them. If an engine is unavailable or not used, then a
cache for it will *not* actually be allocated.
*/

use log::debug;
use regex_automata::nfa::thompson::NFA;
use regex_automata::util::prefilter::Prefilter;
use regex_automata::util::primitives::NonMaxUsize;
use regex_automata::{dfa, hybrid, HalfMatch, Match, MatchKind, PatternID};

use crate::cursor::Cursor;
use crate::engines::pikevm;
use crate::meta::error::{BuildError, RetryFailError};
use crate::meta::regex::RegexInfo;
use crate::Input;

#[derive(Debug)]
pub(crate) struct PikeVM(PikeVMEngine);

impl PikeVM {
    pub(crate) fn new(
        info: &RegexInfo,
        pre: Option<Prefilter>,
        nfa: &NFA,
    ) -> Result<PikeVM, BuildError> {
        PikeVMEngine::new(info, pre, nfa).map(PikeVM)
    }

    pub(crate) fn create_cache(&self) -> PikeVMCache {
        PikeVMCache::new(self)
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn get(&self) -> &PikeVMEngine {
        &self.0
    }
}

#[derive(Debug)]
pub(crate) struct PikeVMEngine(pikevm::PikeVM);

impl PikeVMEngine {
    pub(crate) fn new(
        info: &RegexInfo,
        pre: Option<Prefilter>,
        nfa: &NFA,
    ) -> Result<PikeVMEngine, BuildError> {
        let pikevm_config =
            pikevm::Config::new().match_kind(info.config().get_match_kind()).prefilter(pre);
        let engine = pikevm::Builder::new()
            .configure(pikevm_config)
            .build_from_nfa(nfa.clone())
            .map_err(BuildError::nfa)?;
        debug!("PikeVM built");
        Ok(PikeVMEngine(engine))
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn is_match(&self, cache: &mut PikeVMCache, input: &mut Input<impl Cursor>) -> bool {
        crate::engines::pikevm::is_match(&self.0, cache.0.as_mut().unwrap(), input)
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn search_slots(
        &self,
        cache: &mut PikeVMCache,
        input: &mut Input<impl Cursor>,
        slots: &mut [Option<NonMaxUsize>],
    ) -> Option<PatternID> {
        crate::engines::pikevm::search_slots(&self.0, cache.0.as_mut().unwrap(), input, slots)
    }

    // #[cfg_attr(feature = "perf-inline", inline(always))]
    // pub(crate) fn which_overlapping_matches(
    //     &self,
    //     cache: &mut PikeVMCache,
    //     input: &mut Input<impl Cursor>,
    //     patset: &mut PatternSet,
    // ) {
    //     self.0.which_overlapping_matches(cache.0.as_mut().unwrap(), input, patset)
    // }
}

#[derive(Clone, Debug)]
pub(crate) struct PikeVMCache(Option<pikevm::Cache>);

impl PikeVMCache {
    pub(crate) fn none() -> PikeVMCache {
        PikeVMCache(None)
    }

    pub(crate) fn new(builder: &PikeVM) -> PikeVMCache {
        PikeVMCache(Some(pikevm::Cache::new(&builder.get().0)))
    }

    pub(crate) fn reset(&mut self, builder: &PikeVM) {
        self.0.as_mut().unwrap().reset(&builder.get().0);
    }

    pub(crate) fn memory_usage(&self) -> usize {
        self.0.as_ref().map_or(0, |c| c.memory_usage())
    }
}

#[derive(Debug)]
pub(crate) struct Hybrid(Option<HybridEngine>);

impl Hybrid {
    pub(crate) fn none() -> Hybrid {
        Hybrid(None)
    }

    pub(crate) fn new(info: &RegexInfo, pre: Option<Prefilter>, nfa: &NFA, nfarev: &NFA) -> Hybrid {
        Hybrid(HybridEngine::new(info, pre, nfa, nfarev))
    }

    pub(crate) fn create_cache(&self) -> HybridCache {
        HybridCache::new(self)
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn get(&self, _input: &mut Input<impl Cursor>) -> Option<&HybridEngine> {
        let engine = self.0.as_ref()?;
        Some(engine)
    }

    pub(crate) fn is_some(&self) -> bool {
        self.0.is_some()
    }
}

#[derive(Debug)]
pub(crate) struct HybridEngine(hybrid::regex::Regex);

impl HybridEngine {
    pub(crate) fn new(
        info: &RegexInfo,
        pre: Option<Prefilter>,
        nfa: &NFA,
        nfarev: &NFA,
    ) -> Option<HybridEngine> {
        {
            if !info.config().get_hybrid() {
                return None;
            }
            let dfa_config = hybrid::dfa::Config::new()
                .match_kind(info.config().get_match_kind())
                .prefilter(pre.clone())
                // Enabling this is necessary for ensuring we can service any
                // kind of 'Input' search without error. For the lazy DFA,
                // this is not particularly costly, since the start states are
                // generated lazily.
                .starts_for_each_pattern(true)
                .byte_classes(info.config().get_byte_classes())
                .unicode_word_boundary(true)
                .specialize_start_states(pre.is_some())
                .cache_capacity(info.config().get_hybrid_cache_capacity())
                // This makes it possible for building a lazy DFA to
                // fail even though the NFA has already been built. Namely,
                // if the cache capacity is too small to fit some minimum
                // number of states (which is small, like 4 or 5), then the
                // DFA will refuse to build.
                //
                // We shouldn't enable this to make building always work, since
                // this could cause the allocation of a cache bigger than the
                // provided capacity amount.
                //
                // This is effectively the only reason why building a lazy DFA
                // could fail. If it does, then we simply suppress the error
                // and return None.
                .skip_cache_capacity_check(false)
                // This and enabling heuristic Unicode word boundary support
                // above make it so the lazy DFA can quit at match time.
                .minimum_cache_clear_count(Some(3))
                .minimum_bytes_per_state(Some(10));
            let result = hybrid::dfa::Builder::new()
                .configure(dfa_config.clone())
                .build_from_nfa(nfa.clone());
            let fwd = match result {
                Ok(fwd) => fwd,
                Err(_err) => {
                    debug!("forward lazy DFA failed to build: {}", _err);
                    return None;
                }
            };
            let result = hybrid::dfa::Builder::new()
                .configure(
                    dfa_config
                        .clone()
                        .match_kind(MatchKind::All)
                        .prefilter(None)
                        .specialize_start_states(false),
                )
                .build_from_nfa(nfarev.clone());
            let rev = match result {
                Ok(rev) => rev,
                Err(_err) => {
                    debug!("reverse lazy DFA failed to build: {}", _err);
                    return None;
                }
            };
            let engine = hybrid::regex::Builder::new().build_from_dfas(fwd, rev);
            debug!("lazy DFA built");
            Some(HybridEngine(engine))
        }
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn try_search(
        &self,
        cache: &mut HybridCache,
        input: &mut Input<impl Cursor>,
    ) -> Result<Option<Match>, RetryFailError> {
        let cache = cache.0.as_mut().unwrap();
        crate::engines::hybrid::try_search(&self.0, cache, input).map_err(|e| e.into())
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn try_search_half_fwd(
        &self,
        cache: &mut HybridCache,
        input: &mut Input<impl Cursor>,
    ) -> Result<Option<HalfMatch>, RetryFailError> {
        let fwd = self.0.forward();
        let fwdcache = cache.0.as_mut().unwrap().as_parts_mut().0;
        crate::engines::hybrid::try_search_fwd(fwd, fwdcache, input).map_err(|e| e.into())
    }

    // #[cfg_attr(feature = "perf-inline", inline(always))]
    // pub(crate) fn try_search_half_fwd_stopat(
    //     &self,
    //     cache: &mut HybridCache,
    //     input: &mut Input<impl Cursor>,
    // ) -> Result<Result<HalfMatch, usize>, RetryFailError> {
    //     let dfa = self.0.forward();
    //     let mut cache = cache.0.as_mut().unwrap().as_parts_mut().0;
    //     crate::meta::stopat::hybrid_try_search_half_fwd(dfa, &mut cache, input)
    // }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn try_search_half_rev(
        &self,
        cache: &mut HybridCache,
        input: &mut Input<impl Cursor>,
    ) -> Result<Option<HalfMatch>, RetryFailError> {
        let rev = self.0.reverse();
        let revcache = cache.0.as_mut().unwrap().as_parts_mut().1;
        crate::engines::hybrid::try_search_rev(rev, revcache, input).map_err(|e| e.into())
    }

    // #[cfg_attr(feature = "perf-inline", inline(always))]
    // pub(crate) fn try_search_half_rev_limited(
    //     &self,
    //     cache: &mut HybridCache,
    //     input: &mut Input<impl Cursor>,
    //     min_start: usize,
    // ) -> Result<Option<HalfMatch>, RetryError> {
    //     let dfa = self.0.reverse();
    //     let mut cache = cache.0.as_mut().unwrap().as_parts_mut().1;
    //     crate::meta::limited::hybrid_try_search_half_rev(dfa, &mut cache, input, min_start)
    // }

    // #[inline]
    // pub(crate) fn try_which_overlapping_matches(
    //     &self,
    //     cache: &mut HybridCache,
    //     input: &mut Input<impl Cursor>,
    //     patset: &mut PatternSet,
    // ) -> Result<(), RetryFailError> {
    //         let fwd = self.0.forward();
    //         let mut fwdcache = cache.0.as_mut().unwrap().as_parts_mut().0;
    //         fwd.try_which_overlapping_matches(&mut fwdcache, input, patset).map_err(|e| e.into())
    // }
}

#[derive(Clone, Debug)]
pub(crate) struct HybridCache(Option<hybrid::regex::Cache>);

impl HybridCache {
    pub(crate) fn none() -> HybridCache {
        HybridCache(None)
    }

    pub(crate) fn new(builder: &Hybrid) -> HybridCache {
        HybridCache(builder.0.as_ref().map(|e| e.0.create_cache()))
    }

    pub(crate) fn reset(&mut self, builder: &Hybrid) {
        if let Some(ref e) = builder.0 {
            self.0.as_mut().unwrap().reset(&e.0);
        }
    }

    pub(crate) fn memory_usage(&self) -> usize {
        {
            self.0.as_ref().map_or(0, |c| c.memory_usage())
        }
    }
}

#[derive(Debug)]
pub(crate) struct DFA(Option<DFAEngine>);

impl DFA {
    pub(crate) fn none() -> DFA {
        DFA(None)
    }

    pub(crate) fn new(info: &RegexInfo, pre: Option<Prefilter>, nfa: &NFA, nfarev: &NFA) -> DFA {
        DFA(DFAEngine::new(info, pre, nfa, nfarev))
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn get(&self, _input: &mut Input<impl Cursor>) -> Option<&DFAEngine> {
        let engine = self.0.as_ref()?;
        Some(engine)
    }

    pub(crate) fn is_some(&self) -> bool {
        self.0.is_some()
    }

    pub(crate) fn memory_usage(&self) -> usize {
        self.0.as_ref().map_or(0, |e| e.memory_usage())
    }
}

#[derive(Debug)]
pub(crate) struct DFAEngine(dfa::regex::Regex);

impl DFAEngine {
    pub(crate) fn new(
        info: &RegexInfo,
        pre: Option<Prefilter>,
        nfa: &NFA,
        nfarev: &NFA,
    ) -> Option<DFAEngine> {
        {
            if !info.config().get_dfa() {
                return None;
            }
            // If our NFA is anything but small, don't even bother with a DFA.
            if let Some(state_limit) = info.config().get_dfa_state_limit() {
                if nfa.states().len() > state_limit {
                    debug!(
                        "skipping full DFA because NFA has {} states, \
                         which exceeds the heuristic limit of {}",
                        nfa.states().len(),
                        state_limit,
                    );
                    return None;
                }
            }
            // We cut the size limit in four because the total heap used by
            // DFA construction is determinization aux memory and the DFA
            // itself, and those things are configured independently in the
            // lower level DFA builder API. And then split that in two because
            // of forward and reverse DFAs.
            let size_limit = info.config().get_dfa_size_limit().map(|n| n / 4);
            let dfa_config = dfa::dense::Config::new()
                .match_kind(info.config().get_match_kind())
                .prefilter(pre.clone())
                // Enabling this is necessary for ensuring we can service any
                // kind of 'Input' search without error. For the full DFA, this
                // can be quite costly. But since we have such a small bound
                // on the size of the DFA, in practice, any multl-regexes are
                // probably going to blow the limit anyway.
                .starts_for_each_pattern(true)
                .byte_classes(info.config().get_byte_classes())
                .unicode_word_boundary(true)
                .specialize_start_states(pre.is_some())
                .determinize_size_limit(size_limit)
                .dfa_size_limit(size_limit);
            let result =
                dfa::dense::Builder::new().configure(dfa_config.clone()).build_from_nfa(nfa);
            let fwd = match result {
                Ok(fwd) => fwd,
                Err(_err) => {
                    debug!("forward full DFA failed to build: {}", _err);
                    return None;
                }
            };
            let result = dfa::dense::Builder::new()
                .configure(
                    dfa_config
                        .clone()
                        // We never need unanchored reverse searches, so
                        // there's no point in building it into the DFA, which
                        // WILL take more space. (This isn't done for the lazy
                        // DFA because the DFA is, well, lazy. It doesn't pay
                        // the cost for supporting unanchored searches unless
                        // you actually do an unanchored search, which we
                        // don't.)
                        .start_kind(dfa::StartKind::Anchored)
                        .match_kind(MatchKind::All)
                        .prefilter(None)
                        .specialize_start_states(false),
                )
                .build_from_nfa(nfarev);
            let rev = match result {
                Ok(rev) => rev,
                Err(_err) => {
                    debug!("reverse full DFA failed to build: {}", _err);
                    return None;
                }
            };
            let engine = dfa::regex::Builder::new().build_from_dfas(fwd, rev);
            debug!(
                "fully compiled forward and reverse DFAs built, {} bytes",
                engine.forward().memory_usage() + engine.reverse().memory_usage(),
            );
            Some(DFAEngine(engine))
        }
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn try_search(
        &self,
        input: &mut Input<impl Cursor>,
    ) -> Result<Option<Match>, RetryFailError> {
        crate::engines::dfa::try_search(&self.0, input).map_err(|err| err.into())
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn try_search_half_fwd(
        &self,
        input: &mut Input<impl Cursor>,
    ) -> Result<Option<HalfMatch>, RetryFailError> {
        crate::engines::dfa::try_search_fwd(self.0.forward(), input).map_err(|e| e.into())
    }

    // #[cfg_attr(feature = "perf-inline", inline(always))]
    // pub(crate) fn try_search_half_fwd_stopat(
    //     &self,
    //     input: &mut Input<impl Cursor>,
    // ) -> Result<Result<HalfMatch, usize>, RetryFailError> {
    //         let dfa = self.0.forward();
    //         crate::meta::stopat::dfa_try_search_half_fwd(dfa, input)
    // }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn try_search_half_rev(
        &self,
        input: &mut Input<impl Cursor>,
    ) -> Result<Option<HalfMatch>, RetryFailError> {
        crate::engines::dfa::try_search_rev(self.0.reverse(), input).map_err(|e| e.into())
    }

    // #[cfg_attr(feature = "perf-inline", inline(always))]
    // pub(crate) fn try_search_half_rev_limited(
    //     &self,
    //     input: &mut Input<impl Cursor>,
    //     min_start: usize,
    // ) -> Result<Option<HalfMatch>, RetryError> {
    //     let dfa = self.0.reverse();
    //     crate::meta::limited::dfa_try_search_half_rev(dfa, input, min_start)
    // }

    // #[inline]
    // pub(crate) fn try_which_overlapping_matches(
    //     &self,
    //     input: &mut Input<impl Cursor>,
    //     patset: &mut PatternSet,
    // ) -> Result<(), RetryFailError> {
    //         use crate::dfa::Automaton;
    //         self.0.forward().try_which_overlapping_matches(input, patset).map_err(|e| e.into())
    // }

    pub(crate) fn memory_usage(&self) -> usize {
        self.0.forward().memory_usage() + self.0.reverse().memory_usage()
    }
}

// #[derive(Debug)]
// pub(crate) struct ReverseHybrid(Option<ReverseHybridEngine>);

// impl ReverseHybrid {
//     pub(crate) fn none() -> ReverseHybrid {
//         ReverseHybrid(None)
//     }

//     pub(crate) fn new(info: &RegexInfo, nfarev: &NFA) -> ReverseHybrid {
//         ReverseHybrid(ReverseHybridEngine::new(info, nfarev))
//     }

//     pub(crate) fn create_cache(&self) -> ReverseHybridCache {
//         ReverseHybridCache::new(self)
//     }

//     #[cfg_attr(feature = "perf-inline", inline(always))]
//     pub(crate) fn get(&self, _input: &mut Input<impl Cursor>) -> Option<&ReverseHybridEngine> {
//         let engine = self.0.as_ref()?;
//         Some(engine)
//     }
// }

// #[derive(Debug)]
// pub(crate) struct ReverseHybridEngine(hybrid::dfa::DFA);

// impl ReverseHybridEngine {
//     pub(crate) fn new(info: &RegexInfo, nfarev: &NFA) -> Option<ReverseHybridEngine> {
//         if !info.config().get_hybrid() {
//             return None;
//         }
//         // Since we only use this for reverse searches, we can hard-code
//         // a number of things like match semantics, prefilters, starts
//         // for each pattern and so on.
//         let dfa_config = hybrid::dfa::Config::new()
//             .match_kind(MatchKind::All)
//             .prefilter(None)
//             .starts_for_each_pattern(false)
//             .byte_classes(info.config().get_byte_classes())
//             .unicode_word_boundary(true)
//             .specialize_start_states(false)
//             .cache_capacity(info.config().get_hybrid_cache_capacity())
//             .skip_cache_capacity_check(false)
//             .minimum_cache_clear_count(Some(3))
//             .minimum_bytes_per_state(Some(10));
//         let result =
//             hybrid::dfa::Builder::new().configure(dfa_config).build_from_nfa(nfarev.clone());
//         let rev = match result {
//             Ok(rev) => rev,
//             Err(_err) => {
//                 debug!("lazy reverse DFA failed to build: {}", _err);
//                 return None;
//             }
//         };
//         debug!("lazy reverse DFA built");
//         Some(ReverseHybridEngine(rev))
//     }

//     #[cfg_attr(feature = "perf-inline", inline(always))]
//     pub(crate) fn try_search_half_rev_limited(
//         &self,
//         cache: &mut ReverseHybridCache,
//         input: &mut Input<impl Cursor>,
//         min_start: usize,
//     ) -> Result<Option<HalfMatch>, RetryError> {
//         let dfa = &self.0;
//         let mut cache = cache.0.as_mut().unwrap();
//         crate::meta::limited::hybrid_try_search_half_rev(dfa, &mut cache, input, min_start)
//     }
// }

// #[derive(Clone, Debug)]
// pub(crate) struct ReverseHybridCache(
//     #[cfg(feature = "hybrid")] Option<hybrid::dfa::Cache>,
//     #[cfg(not(feature = "hybrid"))] (),
// );

// impl ReverseHybridCache {
//     pub(crate) fn none() -> ReverseHybridCache {
//         #[cfg(feature = "hybrid")]
//         {
//             ReverseHybridCache(None)
//         }
//         #[cfg(not(feature = "hybrid"))]
//         {
//             ReverseHybridCache(())
//         }
//     }

//     pub(crate) fn new(builder: &ReverseHybrid) -> ReverseHybridCache {
//         #[cfg(feature = "hybrid")]
//         {
//             ReverseHybridCache(builder.0.as_ref().map(|e| e.0.create_cache()))
//         }
//         #[cfg(not(feature = "hybrid"))]
//         {
//             ReverseHybridCache(())
//         }
//     }

//     pub(crate) fn reset(&mut self, builder: &ReverseHybrid) {
//         #[cfg(feature = "hybrid")]
//         if let Some(ref e) = builder.0 {
//             self.0.as_mut().unwrap().reset(&e.0);
//         }
//     }

//     pub(crate) fn memory_usage(&self) -> usize {
//         #[cfg(feature = "hybrid")]
//         {
//             self.0.as_ref().map_or(0, |c| c.memory_usage())
//         }
//         #[cfg(not(feature = "hybrid"))]
//         {
//             0
//         }
//     }
// }

// #[derive(Debug)]
// pub(crate) struct ReverseDFA(Option<ReverseDFAEngine>);

// impl ReverseDFA {
//     pub(crate) fn none() -> ReverseDFA {
//         ReverseDFA(None)
//     }

//     pub(crate) fn new(info: &RegexInfo, nfarev: &NFA) -> ReverseDFA {
//         ReverseDFA(ReverseDFAEngine::new(info, nfarev))
//     }

//     #[cfg_attr(feature = "perf-inline", inline(always))]
//     pub(crate) fn get(&self, _input: &mut Input<impl Cursor>) -> Option<&ReverseDFAEngine> {
//         let engine = self.0.as_ref()?;
//         Some(engine)
//     }

//     pub(crate) fn is_some(&self) -> bool {
//         self.0.is_some()
//     }

//     pub(crate) fn memory_usage(&self) -> usize {
//         self.0.as_ref().map_or(0, |e| e.memory_usage())
//     }
// }

// #[derive(Debug)]
// pub(crate) struct ReverseDFAEngine(
//     #[cfg(feature = "dfa-build")] dfa::dense::DFA<Vec<u32>>,
//     #[cfg(not(feature = "dfa-build"))] (),
// );

// impl ReverseDFAEngine {
//     pub(crate) fn new(info: &RegexInfo, nfarev: &NFA) -> Option<ReverseDFAEngine> {
//         #[cfg(feature = "dfa-build")]
//         {
//             if !info.config().get_dfa() {
//                 return None;
//             }
//             // If our NFA is anything but small, don't even bother with a DFA.
//             if let Some(state_limit) = info.config().get_dfa_state_limit() {
//                 if nfarev.states().len() > state_limit {
//                     debug!(
//                         "skipping full reverse DFA because NFA has {} states, \
//                          which exceeds the heuristic limit of {}",
//                         nfarev.states().len(),
//                         state_limit,
//                     );
//                     return None;
//                 }
//             }
//             // We cut the size limit in two because the total heap used by DFA
//             // construction is determinization aux memory and the DFA itself,
//             // and those things are configured independently in the lower level
//             // DFA builder API.
//             let size_limit = info.config().get_dfa_size_limit().map(|n| n / 2);
//             // Since we only use this for reverse searches, we can hard-code
//             // a number of things like match semantics, prefilters, starts
//             // for each pattern and so on. We also disable acceleration since
//             // it's incompatible with limited searches (which is the only
//             // operation we support for this kind of engine at the moment).
//             let dfa_config = dfa::dense::Config::new()
//                 .match_kind(MatchKind::All)
//                 .prefilter(None)
//                 .accelerate(false)
//                 .start_kind(dfa::StartKind::Anchored)
//                 .starts_for_each_pattern(false)
//                 .byte_classes(info.config().get_byte_classes())
//                 .unicode_word_boundary(true)
//                 .specialize_start_states(false)
//                 .determinize_size_limit(size_limit)
//                 .dfa_size_limit(size_limit);
//             let result = dfa::dense::Builder::new().configure(dfa_config).build_from_nfa(&nfarev);
//             let rev = match result {
//                 Ok(rev) => rev,
//                 Err(_err) => {
//                     debug!("full reverse DFA failed to build: {}", _err);
//                     return None;
//                 }
//             };
//             debug!("fully compiled reverse DFA built, {} bytes", rev.memory_usage());
//             Some(ReverseDFAEngine(rev))
//         }
//         #[cfg(not(feature = "dfa-build"))]
//         {
//             None
//         }
//     }

//     #[cfg_attr(feature = "perf-inline", inline(always))]
//     pub(crate) fn try_search_half_rev_limited(
//         &self,
//         input: &mut Input<impl Cursor>,
//         min_start: usize,
//     ) -> Result<Option<HalfMatch>, RetryError> {
//         #[cfg(feature = "dfa-build")]
//         {
//             let dfa = &self.0;
//             crate::meta::limited::dfa_try_search_half_rev(dfa, input, min_start)
//         }
//         #[cfg(not(feature = "dfa-build"))]
//         {
//             // Impossible to reach because this engine is never constructed
//             // if the requisite features aren't enabled.
//             unreachable!()
//         }
//     }

//     pub(crate) fn memory_usage(&self) -> usize {
//         #[cfg(feature = "dfa-build")]
//         {
//             self.0.memory_usage()
//         }
//         #[cfg(not(feature = "dfa-build"))]
//         {
//             // Impossible to reach because this engine is never constructed
//             // if the requisite features aren't enabled.
//             unreachable!()
//         }
//     }
// }
