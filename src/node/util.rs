use traits::{Leaf, PathInfo, SplitLeaf, SubOrd, SumInfo};
use super::{Node, NodesPtr, balanced_split};

use std::cmp::Ordering;
use std::mem;

use arrayvec::ArrayVec;

#[derive(Clone)]
pub struct InternalT<L: Leaf, NP> {
    pub(super) info: L::Info,
    pub(super) height: usize, // > 0
    pub(super) nodes: NP,
}

impl<L: Leaf, NP: NodesPtr<L>> InternalT<L, NP> {
    fn summarize(nodes: &NP) -> (L::Info, usize) {
        let height = nodes[0].height() + 1;
        let mut info = nodes[0].info();
        for child in &nodes[1..] {
            assert_eq!(height, child.height() + 1);
            info = info.gather(child.info());
        }
        (info, height)
    }

    pub(crate) fn from_nodes(nodes: NP) -> Self {
        assert_ne!(nodes.len(), 0);
        let (info, height) = Self::summarize(&nodes);
        InternalT { info, height, nodes }
    }

    pub(crate) fn merge_maybe_split(&mut self, mut other: Self) -> Option<Self> {
        debug_assert_eq!(self.height, other.height);
        let merged_info = self.info.gather(other.info);
        let (len1, len2) = (self.nodes.len(), other.nodes.len());
        if len1 + len2 <= NP::max_size() {
            NP::make_mut(&mut self.nodes).extend(NP::make_mut(&mut other.nodes).drain(..));
            debug_assert_eq!(self.nodes.len(), len1 + len2);
            self.info = merged_info;
            None
        } else {
            if len1 < NP::min_size() || len2 < NP::min_size() {
                let (newlen1, newlen2) = balanced_split::<L, NP>(len1 + len2);
                if len1 > len2 {
                    let other_nodes = NP::make_mut(&mut other.nodes);
                    let mut tmp_other_nodes = ArrayVec::<NP::Array>::new();
                    tmp_other_nodes.extend(NP::make_mut(&mut self.nodes).drain(newlen1..));
                    tmp_other_nodes.extend(other_nodes.drain(..));
                    mem::swap(other_nodes, &mut tmp_other_nodes);
                } else {
                    let drain2 = len2 - newlen2;
                    NP::make_mut(&mut self.nodes).extend(NP::make_mut(&mut other.nodes).drain(..drain2));
                }
                debug_assert_eq!(self.nodes.len() + other.nodes.len(), len1 + len2);
                self.info = Self::summarize(&self.nodes).0;
                other.info = Self::summarize(&other.nodes).0;
            }
            Some(other)
        }
    }
}

#[derive(Clone)]
pub struct LeafT<L: Leaf> {
    pub(super) info: L::Info,
    pub(super) val: L,
}

impl<L: Leaf> LeafT<L> {
    pub(crate) fn from_value(leaf: L) -> Self {
        LeafT {
            info: leaf.compute_info(),
            val: leaf,
        }
    }

    pub(crate) fn merge_maybe_split(&mut self, other: Self) -> Option<Self> {
        let maybe_split = self.val.merge_maybe_split(other.val).map(LeafT::from_value);
        if maybe_split.is_some() {
            self.info = self.val.compute_info();
        } else {
            self.info = self.info.gather(other.info);
        }
        maybe_split
    }

    pub(crate) fn split_off<PI, PS>(&mut self, start: PI, needle: PS) -> Option<Self>
        where L: SplitLeaf<PI, PS>,
              PI: PathInfo<L::Info>,
              PS: SubOrd<PI>,
    {
        match self.val.split_off(start, needle) {
            Some(split_val) => {
                self.info = self.val.compute_info();
                Some(Self::from_value(split_val))
            }
            None => None,
        }
    }
}

/// Right-exclusive range.
#[derive(Clone, Copy)]
pub struct PathRange<PS: Copy> {
    pub left: PS,
    pub right: PS,
}

impl<PS: Copy> PathRange<PS> {
    pub fn is_proper(self) -> bool
        where PS: Ord,
    {
        self.left <= self.right
    }

    pub fn is_empty(self) -> bool
        where PS: Ord,
    {
        self.left >= self.right
    }

    /// Check whether `needle` is out of range, to the left of `self`.
    pub fn starts_after<I: SumInfo, PI: PathInfo<I>>(self, needle: &PI) -> bool
        where PS: SubOrd<PI>,
    {
        match self.left.sub_cmp(needle) {
            Ordering::Greater => true, // self.left > needle
            _ => false,
        }
    }

    /// Check whether `needle` is out of range, to the right of `self`.
    pub fn ends_before<I: SumInfo, PI: PathInfo<I>>(self, needle: &PI) -> bool
        where PS: SubOrd<PI>,
    {
        match self.right.sub_cmp(needle) {
            Ordering::Less | Ordering::Equal => true, // self.right <= needle
            _ => false,
        }
    }
}

pub enum RemoveResult<L: Leaf, NP: NodesPtr<L>> {
    NothingToDo(Node<L, NP>),
    FullyRemoved(Node<L, NP>),
    RangeRemoved {
        remaining: Node<L, NP>,
        removed: Node<L, NP>
    },
}

#[derive(Debug)]
pub struct LeafRef<'a, L: Leaf + 'a, PI: PathInfo<L::Info>> {
    pub leaf: &'a L,
    pub info: L::Info,
    pub before: PI,
    pub after: PI,
}
