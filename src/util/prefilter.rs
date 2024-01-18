/*!
Defines a prefilter for accelerating regex searches.

A prefilter can be created by building a [`Prefilter`] value.

A prefilter represents one of the most important optimizations available for
accelerating regex searches. The idea of a prefilter is to very quickly find
candidate locations in a haystack where a regex _could_ match. Once a candidate
is found, it is then intended for the regex engine to run at that position to
determine whether the candidate is a match or a false positive.

In the aforementioned description of the prefilter optimization also lay its
demise. Namely, if a prefilter has a high false positive rate and it produces
lots of candidates, then a prefilter can overall make a regex search slower.
It can run more slowly because more time is spent ping-ponging between the
prefilter search and the regex engine attempting to confirm each candidate as
a match. This ping-ponging has overhead that adds up, and is exacerbated by
a high false positive rate.

Nevertheless, the optimization is still generally worth performing in most
cases. Particularly given just how much throughput can be improved. (It is not
uncommon for prefilter optimizations to improve throughput by one or two orders
of magnitude.)

Typically a prefilter is used to find occurrences of literal prefixes from a
regex pattern, but this isn't required. A prefilter can be used to look for
suffixes or even inner literals.

Note that as of now, prefilters throw away information about which pattern
each literal comes from. In other words, when a prefilter finds a match,
there's no way to know which pattern (or patterns) it came from. Therefore,
in order to confirm a match, you'll have to check all of the patterns by
running the full regex engine.
*/

use log::debug;
use regex_automata::MatchKind;
use regex_syntax::hir::{literal, Hir};

/// Extracts all of the prefix literals from the given HIR expressions into a
/// single `Seq`. The literals in the sequence are ordered with respect to the
/// order of the given HIR expressions and consistent with the match semantics
/// given.
///
/// The sequence returned is "optimized." That is, they may be shrunk or even
/// truncated according to heuristics with the intent of making them more
/// useful as a prefilter. (Which translates to both using faster algorithms
/// and minimizing the false positive rate.)
///
/// Note that this erases any connection between the literals and which pattern
/// (or patterns) they came from.
///
/// The match kind given must correspond to the match semantics of the regex
/// that is represented by the HIRs given. The match semantics may change the
/// literal sequence returned.
pub(crate) fn prefixes<H>(kind: MatchKind, hirs: &[H]) -> literal::Seq
where
    H: core::borrow::Borrow<Hir>,
{
    let mut extractor = literal::Extractor::new();
    extractor.kind(literal::ExtractKind::Prefix);

    let mut prefixes = literal::Seq::empty();
    for hir in hirs {
        prefixes.union(&mut extractor.extract(hir.borrow()));
    }
    debug!(
        "prefixes (len={:?}, exact={:?}) extracted before optimization: {:?}",
        prefixes.len(),
        prefixes.is_exact(),
        prefixes
    );
    match kind {
        MatchKind::All => {
            prefixes.sort();
            prefixes.dedup();
        }
        MatchKind::LeftmostFirst => {
            prefixes.optimize_for_prefix_by_preference();
        }
        _ => unreachable!(),
    }
    debug!(
        "prefixes (len={:?}, exact={:?}) extracted after optimization: {:?}",
        prefixes.len(),
        prefixes.is_exact(),
        prefixes
    );
    prefixes
}
