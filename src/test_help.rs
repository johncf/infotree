use cursor::{Cursor};//, CursorMut};
use node::{Node, Rc16};
use traits::{Info, Leaf, PathInfo, SubOrd};

use std::cmp;

pub fn rand_usize(max: usize) -> usize {
    ::rand::random::<usize>() % max
}

/// A useful type alias for easy initialization of `Cursor`.
pub type CursorT<'a, L> = Cursor<'a, L, ()>;

//pub type CursorMutT<L> = CursorMut<L, ()>;

/// A useful type alias for easy initialization of `Node`.
pub type NodeRc<L> = Node<L, Rc16<L>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListLeaf(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListInfo {
    pub count: usize,
    pub sum: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListPath {
    pub index: usize,
    pub run: usize,
}
pub struct ListIndex(pub usize);
pub struct ListRun(pub usize);

impl Leaf for ListLeaf {
    type Info = ListInfo;
    fn compute_info(&self) -> ListInfo {
        ListInfo {
            count: 1,
            sum: self.0,
        }
    }
}

impl Info for ListInfo {
    fn gather(self, other: Self) -> Self {
        ListInfo {
            count: self.count + other.count,
            sum: self.sum + other.sum,
        }
    }
}

impl PathInfo<ListInfo> for ListPath {
    fn extend(self, prev: ListInfo) -> Self {
        ListPath {
            index: self.index + prev.count,
            run: self.run + prev.sum,
        }
    }

    fn extend_inv(self, curr: ListInfo) -> Self {
        ListPath {
            index: self.index - curr.count,
            run: self.run - curr.sum,
        }
    }

    fn identity() -> Self {
        ListPath {
            index: 0,
            run: 0,
        }
    }
}

impl SubOrd<ListPath> for ListIndex {
    fn sub_cmp(&self, rhs: &ListPath) -> cmp::Ordering {
        self.0.cmp(&rhs.index)
    }
}

impl SubOrd<ListPath> for ListRun {
    fn sub_cmp(&self, rhs: &ListPath) -> cmp::Ordering {
        self.0.cmp(&rhs.run)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SetLeaf(pub char, pub usize);

#[derive(Clone, Copy, Debug)]
pub struct SetInfo {
    pub min: SetLeaf,
    pub max: SetLeaf,
}

pub struct MinChar(pub char);
pub struct MaxChar(pub char);
pub struct MinLeaf(pub SetLeaf);
pub struct MaxLeaf(pub SetLeaf);

impl Leaf for SetLeaf {
    type Info = SetInfo;
    fn compute_info(&self) -> SetInfo {
        SetInfo {
            min: *self,
            max: *self,
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
        self.0.cmp(&rhs.min.0)
    }
}

impl SubOrd<SetInfo> for MaxChar {
    fn sub_cmp(&self, rhs: &SetInfo) -> cmp::Ordering {
        self.0.cmp(&rhs.max.0)
    }
}

impl SubOrd<SetInfo> for MinLeaf {
    fn sub_cmp(&self, rhs: &SetInfo) -> cmp::Ordering {
        self.0.cmp(&rhs.min)
    }
}

impl SubOrd<SetInfo> for MaxLeaf {
    fn sub_cmp(&self, rhs: &SetInfo) -> cmp::Ordering {
        self.0.cmp(&rhs.max)
    }
}

//#[test]
//fn print() {
//    use ::std::mem; use ::{CursorMut};
//    panic!("printed {}", mem::size_of::<CursorMut<ListLeaf, usize>>());
//}
