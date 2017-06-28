//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! Both design and implementation are heavily based on [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope
extern crate arrayvec;
extern crate mines;

use std::cmp;
use std::ops::{Deref, DerefMut};

use arrayvec::ArrayVec;
use mines::boom;

pub mod node;
pub mod cursor;
pub mod cursor_mut;

pub mod ext;

pub use node::Node;
pub use ext::{PathInfo, SubOrd};
pub use cursor::Cursor;
pub use cursor_mut::CursorMut;

const MIN_CHILDREN: usize = 8;
const MAX_CHILDREN: usize = 16;

//trait Mutable: Deref {
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

/// The value stored in a leaf node should implement this trait.
///
/// Note: If cloning a leaf is expensive, consider wrapping it in `Arc`.
pub trait Leaf: Clone {
    type Info: Info;

    fn compute_info(&self) -> Self::Info;
}

/// Metadata that need to be gathered hierarchically over the tree.
pub trait Info: Copy {
    /// Used when gathering info from children to parent nodes. Should probably be commutative and
    /// associative.
    fn gather(self, other: Self) -> Self;
}

impl Info for () {
    #[inline]
    fn gather(self, _: ()) { }
}

impl Info for usize {
    #[inline]
    fn gather(self, other: usize) -> usize { self + other }
}

fn balanced_split(total: usize) -> (usize, usize) {
    debug_assert!(MAX_CHILDREN <= total && total <= 2*MAX_CHILDREN);
    // Make left heavy. Splitting at midpoint is another option
    let n_left = cmp::min(total - MIN_CHILDREN, MAX_CHILDREN);
    let n_right = total - n_left;
    debug_assert!(MIN_CHILDREN <= n_left && n_left <= MAX_CHILDREN);
    debug_assert!(MIN_CHILDREN <= n_right && n_right <= MAX_CHILDREN);
    (n_left, n_right)
}

#[cfg(test)]
mod test_help;
