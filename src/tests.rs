use crate::{
    test_rope::{DeterministicSlices, RandomSlices},
    Input,
};

use {
    crate::meta::{self, Regex},
    anyhow::Result,
    regex_automata::util::syntax,
    regex_automata::MatchKind,
    regex_test::{CompiledRegex, Match, RegexTest, SearchKind, Span, TestResult, TestRunner},
};

fn suite() -> anyhow::Result<regex_test::RegexTests> {
    let mut tests = regex_test::RegexTests::new();
    macro_rules! load {
        ($name:expr) => {{
            const DATA: &[u8] = include_bytes!(concat!("../../regex/testdata/", $name, ".toml"));
            tests.load_slice($name, DATA)?;
        }};
    }

    load!("anchored");
    load!("bytes");
    load!("crazy");
    load!("crlf");
    load!("earliest");
    load!("empty");
    load!("expensive");
    load!("flags");
    load!("iter");
    load!("leftmost-all");
    load!("line-terminator");
    load!("misc");
    load!("multiline");
    load!("no-unicode");
    // load!("overlapping");
    load!("regression");
    load!("set");
    load!("substring");
    load!("unicode");
    // load!("utf8");
    load!("word-boundary");
    // load!("word-boundary-special");
    load!("fowler/basic");
    load!("fowler/nullsubexpr");
    load!("fowler/repetition");

    Ok(tests)
}

/// Configure a regex_automata::Input with the given test configuration.
fn create_input(test: &regex_test::RegexTest) -> crate::Input<RandomSlices> {
    use regex_automata::Anchored;

    let bounds = test.bounds();
    let anchored = if test.anchored() { Anchored::Yes } else { Anchored::No };
    let mut input = crate::Input::new(crate::test_rope::RandomSlices::new(test.haystack()))
        .range(bounds.start..bounds.end);
    input.anchored(anchored);
    input
}

/// Convert capture matches into the test suite's capture values.
///
/// The given captures must represent a valid match, where the first capturing
/// group has a non-None span. Otherwise this panics.
fn testify_captures(caps: &regex_automata::util::captures::Captures) -> regex_test::Captures {
    assert!(caps.is_match(), "expected captures to represent a match");
    let spans =
        caps.iter().map(|group| group.map(|m| regex_test::Span { start: m.start, end: m.end }));
    // These unwraps are OK because we assume our 'caps' represents a match,
    // and a match always gives a non-zero number of groups with the first
    // group being non-None.
    regex_test::Captures::new(caps.pattern().unwrap().as_usize(), spans).unwrap()
}

const BLACKLIST: &[&str] = &[
    // These 'earliest' tests are blacklisted because the meta searcher doesn't
    // give the same offsets that the test expects. This is legal because the
    // 'earliest' routines don't guarantee a particular match offset other
    // than "the earliest the regex engine can report a match." Some regex
    // engines will quit earlier than others. The backtracker, for example,
    // can't really quit before finding the full leftmost-first match. Many of
    // the literal searchers also don't have the ability to quit fully or it's
    // otherwise not worth doing. (A literal searcher not quitting as early as
    // possible usually means looking at a few more bytes. That's no biggie.)
    "earliest/",
];

const RUNS: usize = 50;
/// Tests the default configuration of the meta regex engine.
#[test]
fn default() -> Result<()> {
    let builder = Regex::builder();
    let mut runner = TestRunner::new()?;
    runner
        .expand(&["is_match", "find", "captures"], |test| test.compiles())
        .blacklist_iter(BLACKLIST);
    for _ in 0..=RUNS {
        runner.test_iter(suite()?.iter(), compiler(builder.clone()));
    }
    runner.assert();
    Ok(())
}

/// Tests the default configuration of the meta regex engine.
#[test]
fn multi() -> Result<()> {
    let mut builder = Regex::builder();
    let meta_config = Regex::config()
        .match_kind(MatchKind::LeftmostFirst)
        .utf8_empty(true)
        .line_terminator(10)
        .dfa(true)
        .hybrid(true);
    builder.configure(meta_config).syntax(syntax::Config::new().utf8(true));
    let regex = builder.build("ab|a").unwrap();
    // let regex = builder.build_many(&["ab", "a"]).unwrap();
    // println!("{regex:#?}");
    // for _ in 0..=1000000 {
    // let input = RandomSlices::new(b"xxabc");
    let input = DeterministicSlices::new(&[b"x", b"x", b"a", b"b", b"c"]);
    assert_eq!(regex.find(Input::new(input)).unwrap().range(), 2..4);
    // }
    Ok(())
}

/// Tests the default configuration minus the full DFA.
#[test]
fn no_dfa() -> Result<()> {
    let mut builder = Regex::builder();
    builder.configure(Regex::config().dfa(false));
    let mut runner = TestRunner::new()?;
    runner
        .expand(&["is_match", "find", "captures"], |test| test.compiles())
        .blacklist_iter(BLACKLIST);
    for _ in 0..=RUNS {
        runner.test_iter(suite()?.iter(), compiler(builder.clone()));
    }
    runner.assert();
    Ok(())
}

/// Tests the default configuration minus the full DFA and lazy DFA.
#[test]
fn no_dfa_hybrid() -> Result<()> {
    let mut builder = Regex::builder();
    builder.configure(Regex::config().dfa(false).hybrid(false));
    let mut runner = TestRunner::new()?;
    runner
        .expand(&["is_match", "find", "captures"], |test| test.compiles())
        .blacklist_iter(BLACKLIST);
    for _ in 0..=RUNS {
        runner.test_iter(suite()?.iter(), compiler(builder.clone()));
    }
    runner.assert();
    Ok(())
}

fn compiler(
    mut builder: meta::Builder,
) -> impl FnMut(&RegexTest, &[String]) -> Result<CompiledRegex> {
    move |test, regexes| {
        if !configure_meta_builder(test, &mut builder) {
            return Ok(CompiledRegex::skip());
        }
        // println!("{} {builder:?}", test.full_name());
        let re = builder.build_many(regexes)?;
        Ok(CompiledRegex::compiled(move |test| -> TestResult { run_test(&re, test) }))
    }
}

fn run_test(re: &Regex, test: &RegexTest) -> TestResult {
    let mut input = create_input(test);
    match test.additional_name() {
        "is_match" => TestResult::matched(re.is_match(input)),
        "find" => match test.search_kind() {
            SearchKind::Earliest => {
                input.earliest(true);
                TestResult::matches(
                    re.find_iter(input).take(test.match_limit().unwrap_or(std::usize::MAX)).map(
                        |m| Match {
                            id: m.pattern().as_usize(),
                            span: Span { start: m.start(), end: m.end() },
                        },
                    ),
                )
            }
            SearchKind::Leftmost => TestResult::matches(
                re.find_iter(input).take(test.match_limit().unwrap_or(std::usize::MAX)).map(|m| {
                    Match {
                        id: m.pattern().as_usize(),
                        span: Span { start: m.start(), end: m.end() },
                    }
                }),
            ),
            SearchKind::Overlapping => TestResult::skip(),
        },
        "captures" => match test.search_kind() {
            SearchKind::Earliest => {
                input.earliest(true);
                let it = re
                    .captures_iter(input)
                    .take(test.match_limit().unwrap_or(std::usize::MAX))
                    .map(|caps| testify_captures(&caps));
                TestResult::captures(it)
            }
            SearchKind::Leftmost => {
                let it = re
                    .captures_iter(input)
                    .take(test.match_limit().unwrap_or(std::usize::MAX))
                    .map(|caps| testify_captures(&caps));
                TestResult::captures(it)
            }
            SearchKind::Overlapping => {
                // There is no overlapping regex API that supports captures.
                TestResult::skip()
            }
        },
        name => TestResult::fail(&format!("unrecognized test name: {}", name)),
    }
}

/// Configures the given regex builder with all relevant settings on the given
/// regex test.
///
/// If the regex test has a setting that is unsupported, then this returns
/// false (implying the test should be skipped).
fn configure_meta_builder(test: &RegexTest, builder: &mut meta::Builder) -> bool {
    let match_kind = match test.match_kind() {
        regex_test::MatchKind::All => MatchKind::All,
        regex_test::MatchKind::LeftmostFirst => MatchKind::LeftmostFirst,
        regex_test::MatchKind::LeftmostLongest => return false,
    };
    let meta_config = Regex::config()
        .match_kind(match_kind)
        .utf8_empty(test.utf8())
        .line_terminator(test.line_terminator());
    builder.configure(meta_config).syntax(config_syntax(test));
    true
}

/// Configuration of the regex parser from a regex test.
fn config_syntax(test: &RegexTest) -> syntax::Config {
    syntax::Config::new()
        .case_insensitive(test.case_insensitive())
        .unicode(test.unicode())
        .utf8(test.utf8())
        .line_terminator(test.line_terminator())
}
