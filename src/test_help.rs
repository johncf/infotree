use base::Cursor;
use traits::{Info, Leaf, SubOrd};

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
pub struct SetLeaf(pub char, pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SetInfo {
    pub min: char,
    pub max: char,
}

pub struct MinChar(pub char);
pub struct MaxChar(pub char);

impl Leaf for SetLeaf {
    type Info = SetInfo;
    fn compute_info(&self) -> SetInfo {
        SetInfo {
            min: self.0,
            max: self.0,
        }
    }
}

impl Info for SetInfo {
    fn gather(self, other: Self) -> Self {
        SetInfo {
            min: cmp::min(self.min, other.min),
            max: cmp::max(self.max, other.max),
        }
    }
}

impl SubOrd<SetInfo> for MinChar {
    fn sub_cmp(&self, rhs: &SetInfo) -> cmp::Ordering {
        self.0.cmp(&rhs.min)
    }
}

impl SubOrd<SetInfo> for MaxChar {
    fn sub_cmp(&self, rhs: &SetInfo) -> cmp::Ordering {
        self.0.cmp(&rhs.max)
    }
}

//#[test]
//fn print() {
//    use ::std::mem; use ::{CursorMut};
//    panic!("printed {}", mem::size_of::<CursorMut<TestLeaf, usize>>());
//}
