#![allow(dead_code)]

use node::{Node, Rc16};
use traits::{SumInfo, Leaf, PathInfo, SplitLeaf, SubOrd};

use std::cmp::{self, Ordering};

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

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ListPath {
    pub index: usize,
    pub run: usize,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ListIndex(pub usize);
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
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

impl SplitLeaf<ListPath, ListIndex> for ListLeaf {
    fn split_off(&mut self, before: ListPath, needle: ListIndex) -> Option<Self> {
        if needle.0 >= before.index + 1 {
            None
        } else {
            unreachable!()
        }
    }
}

impl SplitLeaf<ListPath, ListRun> for ListLeaf {
    fn split_off(&mut self, before: ListPath, needle: ListRun) -> Option<Self> {
        if needle.0 >= before.run + self.0 {
            None
        } else if needle.0 > before.run {
            let diff = needle.0 - before.run;
            self.0 -= diff;
            Some(ListLeaf(diff))
        } else {
            unreachable!()
        }
    }
}

impl SumInfo for ListInfo {
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

impl SubOrd<ListPath> for ListIndex {
    fn sub_cmp(&self, rhs: &ListPath) -> Ordering {
        self.0.cmp(&rhs.index)
    }
}

impl SubOrd<ListPath> for ListRun {
    fn sub_cmp(&self, rhs: &ListPath) -> Ordering {
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

impl SumInfo for SetInfo {
    fn gather(self, other: Self) -> Self {
        SetInfo {
            min: cmp::min(self.min, other.min),
            max: cmp::max(self.max, other.max),
        }
    }
}

impl SubOrd<SetInfo> for MinChar {
    fn sub_cmp(&self, rhs: &SetInfo) -> Ordering {
        self.0.cmp(&rhs.min.0)
    }
}

impl SubOrd<SetInfo> for MaxChar {
    fn sub_cmp(&self, rhs: &SetInfo) -> Ordering {
        self.0.cmp(&rhs.max.0)
    }
}

impl SubOrd<SetInfo> for MinLeaf {
    fn sub_cmp(&self, rhs: &SetInfo) -> Ordering {
        self.0.cmp(&rhs.min)
    }
}

impl SubOrd<SetInfo> for MaxLeaf {
    fn sub_cmp(&self, rhs: &SetInfo) -> Ordering {
        self.0.cmp(&rhs.max)
    }
}
