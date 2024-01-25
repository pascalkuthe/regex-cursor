# regex-cursor


This crate provides routines for searching **discontiguous strings** for matches of a [regular expression] (aka "regex"). It is based on [regex-automata] and most of the code is adapted from the various crates in the [regex](https://github.com/rust-lang/regex) repository.

It is intended as a prototype for upstream support for "streaming regex". The cursor based API in this crate is very similar to the API already exposed by `regex`/`regex-automata`. To that end a generic `Cursor` trait is provided that collections can implement.

A sketch of the cursor API is shown below. The string is yielded in multiple byte chunks. Calling advance moves the cursor to the next chunk. Calling backtrack moves the cursor a chunk back. Backtracking is required by this create. That makes it unsuitable for searching fully unbuffered streams like bytes send over a TCP connection. 

``` rust
pub trait Cursor {
    fn chunk(&self) -> &[u8] { .. }
    fn advance(&mut self) -> bool { .. }
    fn bracktrack(&mut self) -> bool { .. }
}
```

Working on this crate showed me that regex backtracks a lot more than expected with most functionality fundamentally requiring backtracking. For network usecases that do not buffer their input the primary usecase would likely be detecting a match (without necessarily requiring the matched byte range). Such usecases can be covered by manually feeding bytes into the hybrid and DFA engines from the regex-automata crate. This approach also has the advantage of allowing the caller to pause the match (async) while waiting for more data allowing the caller to drive the search instead of the engine itself.

The only part of this crate that could be applied to the fully streaming case is the streaming PikeVM implementation. However, there are some limitations:
* only a single search can be run since the PikeVM may look ahead multiple bytes to disambiguate alternative matches
* Prefilters longer than one byte can not work
* utf-8 mode can not be supported (empty matches may occur between unicode boundaries)

Currently, the PikeVM implementation is not written with this use case in mind and may call backtrack unnecessarily, but that could be addressed in the future, but especially the first point is very limiting. The pikevm also does not allow the user to drive the search and would block on network calls for example (no async).

