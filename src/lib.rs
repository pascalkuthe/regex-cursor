pub use cursor::Cursor;
#[cfg(feature = "ropey")]
pub use cursor::RopeyCursor;
pub use input::Input;
pub use regex_automata;

mod cursor;
pub mod engines;
mod input;
mod literal;
mod util;

#[cfg(test)]
mod test_rope;
#[cfg(test)]
mod tests;
