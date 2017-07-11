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

//mod cursor;
//mod cursor_mut;
//mod cursor_nav;

pub mod node;
pub mod traits;

pub mod base {
    pub use node::Node;
    //pub use cursor::Cursor;
    //pub use cursor_mut::CursorMut;
    //pub use cursor_nav::CursorNav;
}

//pub use cursor_nav::actions;

const MIN_CHILDREN: usize = 8;
const MAX_CHILDREN: usize = 16;

type RC<T> = std::sync::Arc<T>; // replace with std::rc::Rc<T> to get significant speed-up.
type NVec<T> = ArrayVec<[T; MAX_CHILDREN]>;

// Maximum height of tree that can be handled by cursor types.
const CURSOR_MAX_HT: usize = 8;
// => Maximum number of elements = MAX_CHILDREN^CURSOR_P2R_SIZE = 16^8 = 2^32

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;

#[cfg(test)]
extern crate rand;

#[cfg(test)]
mod test_help;
