//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! The design and implementation was inspired by [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope
extern crate arrayvec;
extern crate mines;

use arrayvec::ArrayVec;

#[macro_use]
mod macros;

mod cursor;
mod cursor_mut;
mod cursor_nav;

pub mod node;
pub mod traits;

pub use cursor::Cursor;
pub use cursor_mut::CursorMut;
pub use cursor_nav::CursorNav;

pub use cursor_nav::actions;

// Maximum height of tree that can be handled by cursor types.
const CURSOR_MAX_HT: usize = 8;
// => Minimum number of leaves required to exceed a cursor with the above capacity
//          = MAX * MIN^(CURSOR_MAX_HT - 1)
//          = 16 * 8^7 = 2^25 = ~33.5M (for {Arc,Box,Rc}16)

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;

#[cfg(test)]
extern crate rand;

#[cfg(test)]
mod test_help;
