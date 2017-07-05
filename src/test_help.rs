use base::Cursor;
use traits::{Info, Leaf};

use std::cmp;

/// A useful type alias for easy initialization of `Cursor`.
pub type CursorT<'a, L> = Cursor<'a, L, ()>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TestLeaf(pub usize);

impl Leaf for TestLeaf {
    type Info = usize;
    fn compute_info(&self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MinLeaf(pub char, pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MinChar(pub char);

impl Leaf for MinLeaf {
    type Info = MinChar;
    fn compute_info(&self) -> MinChar {
        MinChar(self.0)
    }
}

impl Info for MinChar {
    fn gather(self, other: Self) -> Self {
        cmp::min(self, other)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaxLeaf(pub char, pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MaxChar(pub char);

impl Leaf for MaxLeaf {
    type Info = MaxChar;
    fn compute_info(&self) -> MaxChar {
        MaxChar(self.0)
    }
}

impl Info for MaxChar {
    fn gather(self, other: Self) -> Self {
        cmp::max(self, other)
    }
}

//#[test]
//fn print() {
//    use ::std::mem; use ::{CursorMut};
//    panic!("printed {}", mem::size_of::<CursorMut<TestLeaf, usize>>());
//}
