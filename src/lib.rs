//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! Both design and implementation are heavily based on [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope
extern crate arrayvec;
extern crate mines;

use arrayvec::ArrayVec;

pub mod node;
pub mod cursor;
pub mod cursor_mut;

mod traits;

pub use traits::{Info, Leaf, PathInfo, SubOrd};

pub use node::Node;
pub use cursor::Cursor;
pub use cursor_mut::CursorMut;

const MIN_CHILDREN: usize = 8;
const MAX_CHILDREN: usize = 16;

//trait Mutable: std::ops::Deref {
//    fn make_mut(this: &mut Self) -> &mut Self::Target;
//}
//
//impl<T> Mutable for Box<T> {
//    fn make_mut(this: &mut Box<T>) -> &mut T {
//        &mut *this
//    }
//}
//
// Uncomment the above block, and RC can be assigned the type Box<T>
// This gives around 20-40% speedup!
// Note that `Arc::clone` or `Rc::clone` methods are never used directly (`clone` may be indirectly
// called by `make_mut` if ref-count > 1).

type RC<T> = std::sync::Arc<T>; // replace with std::rc::Rc<T> to get significant speed-up.
type NVec<T> = ArrayVec<[T; MAX_CHILDREN]>;

// Maximum height of tree that can be handled by cursor types.
const CURSOR_MAX_HT: usize = 8;
// => Maximum number of elements = MAX_CHILDREN^CURSOR_P2R_SIZE = 16^8 = 2^32

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;

#[cfg(test)]
mod test_help;
