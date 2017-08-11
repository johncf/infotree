#![allow(dead_code)]

use node::{Node, Rc16};
use traits::{Info, Leaf, PathInfo};

use std::cmp;

pub fn rand_usize(max: usize) -> usize {
    ::rand::random::<usize>() % max
}

/// A useful type alias for easy initialization of `Node`.
pub type NodeRc<L> = Node<L, Rc16<L>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListLeaf(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListInfo {
    pub count: usize,
    pub sum: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ListIndex(pub usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

impl PathInfo<ListInfo> for ListIndex {
    fn extend(self, prev: ListInfo) -> Self {
        ListIndex(self.0 + prev.count)
    }

    fn extend_inv(self, curr: ListInfo) -> Self {
        ListIndex(self.0 - curr.count)
    }
}

impl PathInfo<ListInfo> for ListRun {
    fn extend(self, prev: ListInfo) -> Self {
        ListRun(self.0 + prev.sum)
    }

    fn extend_inv(self, curr: ListInfo) -> Self {
        ListRun(self.0 - curr.sum)
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
