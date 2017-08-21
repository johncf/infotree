use traits::{SumInfo, Leaf, PathInfo, SplitLeaf, SubOrd, SupOrd};

use arrayvec::ArrayVec;

use std::cmp::{self, Ordering};
use std::iter::FromIterator;
use std::mem;

mod links {
    use traits::Leaf;
    use super::Node;

    use arrayvec::{Array, ArrayVec};

    use std::sync::Arc;
    use std::rc::Rc;
    use std::ops::Deref;

    pub trait NodesPtr<L: Leaf>: Clone + Deref<Target=[Node<L, Self>]> {
        type Array: Array<Item=Node<L, Self>>;

        fn new(nodes: ArrayVec<Self::Array>) -> Self;
        fn make_mut(this: &mut Self) -> &mut ArrayVec<Self::Array>;

        fn max_size() -> usize {
            <Self::Array as Array>::capacity()
        }
    }

    def_nodes_ptr_rc!(Arc16, Arc, 16);
    def_nodes_ptr_rc!(Rc16, Rc, 16);
    def_nodes_ptr_box!(Box16, 16);
}

pub use self::links::{NodesPtr, Arc16, Rc16, Box16};

/// The basic building block of a tree.
///
/// `Node` is similar to a B-Tree node, except that it has equal number of entries and branches
/// (as opposed to k elements and k+1 branches in B-Trees). Another difference is that data is
/// stored only in leaf nodes similar to a B+Tree; but unlike B+Trees, there are no direct links
/// between leaf nodes.
#[derive(Clone)]
pub enum Node<L: Leaf, NP> {
    #[doc(hidden)]
    Internal(InternalVal<L, NP>),
    #[doc(hidden)]
    Leaf(LeafVal<L>),
}

#[doc(hidden)]
#[derive(Clone)]
pub struct InternalVal<L: Leaf, NP> {
    info: L::Info,
    height: usize, // > 0
    nodes: NP,
}

#[doc(hidden)]
#[derive(Clone)]
pub struct LeafVal<L: Leaf> {
    info: L::Info,
    val: L,
}

impl<L: Leaf, NP: NodesPtr<L>> Node<L, NP> {
    #[inline]
    pub fn from_leaf(leaf: L) -> Node<L, NP> {
        Node::Leaf(LeafVal::from_value(leaf))
    }

    /// All nodes should be at the same height, panics otherwise.
    #[inline]
    pub fn from_children(nodes: NP) -> Node<L, NP> {
        Node::Internal(InternalVal::from_nodes(nodes))
    }

    /// Tries to unwrap the node into leaf. If node is internal, `Err(self)` is returned.
    pub fn into_leaf(self) -> Result<L, Node<L, NP>> {
        match self {
            Node::Internal(_) => Err(self),
            Node::Leaf(LeafVal { val, .. }) => Ok(val),
        }
    }

    /// Tries to unwrap the node into its children. If node is leaf, `Err(self)` is returned.
    pub fn into_children(self) -> Result<NP, Node<L, NP>> {
        match self {
            Node::Internal(InternalVal { nodes, .. }) => Ok(nodes),
            Node::Leaf(_) => Err(self),
        }
    }

    /// Returns the info for this node, gathered from all its leaves.
    pub fn info(&self) -> L::Info {
        match *self {
            Node::Internal(InternalVal { info, .. })
                | Node::Leaf(LeafVal { info, .. }) => info,
        }
    }

    pub fn height(&self) -> usize {
        match *self {
            Node::Internal(ref int) => int.height,
            Node::Leaf(_) => 0,
        }
    }

    pub fn is_leaf(&self) -> bool {
        match *self {
            Node::Internal(_) => false,
            Node::Leaf(_) => true,
        }
    }

    /// Get the child nodes of this node. If this is a leaf node, this will return an empty slice.
    ///
    /// Note that internal nodes always contain at least one child node.
    pub fn children(&self) -> &[Node<L, NP>] {
        match *self {
            Node::Internal(ref int) => &*int.nodes,
            Node::Leaf(_) => &[],
        }
    }

    /// Get the leaf value if this is a leaf node, otherwise return `None`.
    pub fn leaf(&self) -> Option<&L> {
        match *self {
            Node::Internal(_) => None,
            Node::Leaf(ref leaf) => Some(&leaf.val),
        }
    }

    /// Concatenates two nodes of possibly different heights into a single balanced node.
    pub fn concat(node1: Node<L, NP>, node2: Node<L, NP>) -> Node<L, NP> {
        let (node1, maybe_node2) = Node::maybe_concat(node1, node2);
        if let Some(node2) = maybe_node2 {
            Node::join_two(node1, node2)
        } else {
            node1
        }
    }

    /// Concatenates two nodes of possibly different heights into a single balanced node if the
    /// resulting height does not exceed the maximum height among the original nodes. Otherwise,
    /// splits them into two nodes of equal height.
    pub fn maybe_concat(mut node1: Node<L, NP>, node2: Node<L, NP>) -> (Node<L, NP>, Option<Node<L, NP>>) {
        // This is an optimized version of the following code:
        // https://github.com/google/xi-editor/blob/cbec578/rust/rope/src/tree.rs#L276-L318
        // The originally adapted code (around 3x slower) is probably much easier to read and
        // understand. It may be found in commit ca3344c (line 222) of this file.

        let h1 = node1.height();
        let h2 = node2.height();

        match h1.cmp(&h2) {
            Ordering::Less => {
                let mut children2 = node2.into_children_must();
                let maybe_newnode = {
                    let children2 = NP::make_mut(&mut children2);
                    if h1 == h2 - 1 && node1.has_min_size() {
                        insert_maybe_split(children2, 0, node1)
                            .map(Node::from_children)
                    } else {
                        let (node1_1, maybe_node1_2) = Node::maybe_concat(node1, children2.remove(0));
                        children2.insert(0, node1_1);
                        if let Some(node1_2) = maybe_node1_2 {
                            insert_maybe_split(children2, 1, node1_2)
                                .map(Node::from_children)
                        } else {
                            None
                        }
                    }
                };
                (Node::from_children(children2), maybe_newnode)
            },
            Ordering::Equal => {
                if node1.has_min_size() && node2.has_min_size() {
                    (node1, Some(node2))
                } else {
                    let maybe_node2 = node1.merge_maybe_split(node2);
                    (node1, maybe_node2)
                }
            },
            Ordering::Greater => {
                let mut children1 = node1.into_children_must();
                let maybe_newnode = {
                    let len1 = children1.len();
                    let children1 = NP::make_mut(&mut children1);
                    if h2 == h1 - 1 && node2.has_min_size() {
                        insert_maybe_split(children1, len1, node2)
                            .map(Node::from_children)
                    } else {
                        let (node2_1, maybe_node2_2) = Node::maybe_concat(children1.pop().unwrap(), node2);
                        children1.push(node2_1);
                        if let Some(node2_2) = maybe_node2_2 {
                            insert_maybe_split(children1, len1, node2_2)
                                .map(Node::from_children)
                        } else {
                            None
                        }
                    }
                };
                (Node::from_children(children1), maybe_newnode)
            }
        }
    }

    /// Calls `f` with all leaves satisfying the following conditions:
    ///
    /// ```text
    /// start <= path_info_after
    /// path_info_before < end
    /// ```
    ///
    /// where `path_info_before` is the computed path info when traversal reaches the start of that
    /// node, and `path_info_after = path_info_before.extend(node.info)`.
    ///
    /// `PI::default()` is used as the path info at the beginning of the tree.
    pub fn visit_subseq<'a, PI, PS, F>(&'a self, start: PS, end: PS, mut f: F)
        where PI: PathInfo<L::Info> + Default,
              PS: SubOrd<PI> + Ord + Copy,
              F: FnMut(LeafRef<'a, L, PI>),
    {
        fn __inner<'a, L, NP, PI, PS, F>(node: &'a Node<L, NP>, root: PI, start: PS, end: PS, f: &mut F)
            where L: Leaf,
                  NP: NodesPtr<L>,
                  PI: PathInfo<L::Info>,
                  PS: SubOrd<PI> + Copy,
                  F: FnMut(LeafRef<'a, L, PI>),
        {
            match *node {
                Node::Internal(InternalVal { ref nodes, .. }) => {
                    let mut node_iter = nodes.iter();
                    let mut prev = root;
                    let mut cur_node = None;
                    while let Some(node) = node_iter.next() {
                        let next = prev.extend(node.info());
                        match start.sub_cmp(&next) {
                            Ordering::Greater => prev = next,
                            _ => { // start <= next
                                cur_node = Some(node);
                                break;
                            }
                        }
                    }
                    debug_assert!(cur_node.is_some());
                    while let Some(node) = cur_node {
                        if let Ordering::Less = prev.sup_cmp(&end) { // prev < end
                            __inner(node, prev, start, end, f);
                            prev = prev.extend(node.info())
                        } else {
                            break;
                        }
                        cur_node = node_iter.next();
                    }
                }
                Node::Leaf(LeafVal { ref val, info }) => {
                    let next = root.extend(info);
                    f(LeafRef {
                        leaf: val,
                        info: info,
                        before: root,
                        after: next,
                    });
                }
            }
        }

        if start > end {
            return;
        }

        let root = PI::default();
        let next = root.extend(self.info());
        if let Ordering::Greater = start.sub_cmp(&next) { // start > next
            return;
        }

        __inner(self, root, start, end, &mut f)
    }

    pub fn remove_subseq<PI, PS>(self, range: PathRange<PS>) -> RemoveResult<L, NP>
        where L: SplitLeaf<PI, PS>,
              PI: PathInfo<L::Info> + Default,
              PS: SubOrd<PI> + Ord + Copy,
    {
        use self::RemoveResult::*;
        use self::Ordering::*;

        fn __push<L, NP>(nodes: &mut ArrayVec<NP::Array>, newnode: Node<L, NP>, mut last_ok: bool, c_height: usize) -> bool
            where L: Leaf, NP: NodesPtr<L>,
        {
            let is_ok_child = |n: &Node<L, NP>| n.height() == c_height && n.has_min_size();
            debug_assert!(newnode.height() <= c_height);
            last_ok = last_ok && is_ok_child(&newnode);
            if last_ok || nodes.is_empty() {
                nodes.push(newnode);
            } else {
                let node = nodes.pop().unwrap();
                if newnode.height() == c_height || node.height() == c_height {
                    let (node0, maybe_node1) = Node::maybe_concat(node, newnode);
                    nodes.push(node0);
                    if let Some(node1) = maybe_node1 {
                        nodes.push(node1);
                    }
                    last_ok = true;
                } else {
                    let node = Node::concat(node, newnode);
                    last_ok = is_ok_child(&node);
                    nodes.push(node);
                }
            }
            last_ok
        }

        fn __into_node<L, NP>(mut nodes: ArrayVec<NP::Array>) -> Node<L, NP>
            where L: Leaf, NP: NodesPtr<L>,
        {
            debug_assert!(!nodes.is_empty());
            if nodes.len() == 1 {
                nodes.pop().unwrap()
            } else {
                Node::from_children(NP::new(nodes))
            }
        }

        fn __inner<L, NP, PI, PS>(node: Node<L, NP>, before: PI, range: PathRange<PS>) -> RemoveResult<L, NP>
            where L: SplitLeaf<PI, PS>,
                  NP: NodesPtr<L>,
                  PI: PathInfo<L::Info>,
                  PS: SubOrd<PI> + Copy,
        {
            if range.right_outside(&before) {
                return NothingToDo(node);
            } else {
                let after = before.extend(node.info());
                if range.left_outside(&before) {
                    debug_assert!(!range.left_outside(&after));
                } else {
                    if !range.right_outside(&after) {
                        return FullyRemoved(node);
                    }
                }
            }

            match node {
                Node::Internal(InternalVal { mut nodes, height, .. }) => {
                    let mut nodes_iter = NP::make_mut(&mut nodes).drain(..);
                    let mut before = before;
                    let mut remaining_nodes = ArrayVec::<NP::Array>::new();
                    let mut cur_node = None;
                    while let Some(node) = nodes_iter.next() {
                        let after = before.extend(node.info());
                        if range.left_outside(&after) {
                            remaining_nodes.push(node);
                            before = after;
                        } else {
                            cur_node = Some(node);
                            break;
                        }
                    }
                    debug_assert!(cur_node.is_some());
                    let c_height = height - 1;
                    let mut remaining_last_ok = true;
                    let mut removed_last_ok = true;
                    let mut removed_nodes = ArrayVec::<NP::Array>::new();
                    while let Some(node) = cur_node {
                        let mut remaining_push = |node, last_ok| __push(&mut remaining_nodes, node, last_ok, c_height);
                        let mut removed_push = |node, last_ok| __push(&mut removed_nodes, node, last_ok, c_height);
                        let after = before.extend(node.info());
                        match __inner(node, before, range) {
                            NothingToDo(original) => {
                                remaining_last_ok = remaining_push(original, remaining_last_ok);
                                break;
                            }
                            FullyRemoved(node) => {
                                removed_last_ok = removed_push(node, removed_last_ok);
                            }
                            RangeRemoved { remaining, removed } => {
                                // Note1: remaining and/or removed may not satisfy has_min_size
                                // Note2: this will happen only at the ends (i.e. at most twice)
                                // TODO debug_assert this condition
                                remaining_last_ok = remaining_push(remaining, remaining_last_ok);
                                removed_last_ok = removed_push(removed, removed_last_ok);
                            }
                        }
                        before = after;
                        cur_node = nodes_iter.next();
                    }
                    if let Some(node) = nodes_iter.next() {
                        __push(&mut remaining_nodes, node, remaining_last_ok, c_height);
                        remaining_nodes.extend(nodes_iter);
                    }
                    match (remaining_nodes.is_empty(), removed_nodes.is_empty()) {
                        (true, true) => unreachable!(),
                        (false, true) => NothingToDo(__into_node(remaining_nodes)),
                        (true, false) => FullyRemoved(__into_node(removed_nodes)),
                        (false, false) => RangeRemoved {
                            remaining: __into_node(remaining_nodes),
                            removed: __into_node(removed_nodes),
                        },
                    }
                }
                Node::Leaf(mut leaf_val0) => {
                    if range.left_outside(&before) {
                        match leaf_val0.split_off(before, range.left) {
                            Some(mut leaf_val1) => {
                                match leaf_val1.split_off(before.extend(leaf_val0.info), range.right) {
                                    Some(leaf_val2) => {
                                        let split = leaf_val0.merge_maybe_split(leaf_val2);
                                        assert!(split.is_none(), "Joining parts after removing a sub-range resulted in a split.");
                                    }
                                    None => (),
                                }
                                RangeRemoved {
                                    remaining: Node::Leaf(leaf_val0),
                                    removed: Node::Leaf(leaf_val1),
                                }
                            }
                            None => NothingToDo(Node::Leaf(leaf_val0)),
                        }
                    } else {
                        match leaf_val0.split_off(before, range.right) {
                            Some(leaf_val1) => RangeRemoved {
                                remaining: Node::Leaf(leaf_val0),
                                removed: Node::Leaf(leaf_val1),
                            },
                            None => NothingToDo(Node::Leaf(leaf_val0)),
                        }
                    }
                }
            }
        }

        if range.left >= range.right {
            return NothingToDo(self);
        }

        let before = PI::default();
        let after = before.extend(self.info());
        if range.left_outside(&after) {
            return NothingToDo(self);
        }

        __inner(self, before, range)
    }
}

/// Right-exclusive range.
#[derive(Clone, Copy)]
pub struct PathRange<PS: Copy> {
    pub left: PS,
    pub right: PS,
}

impl<PS: Copy> PathRange<PS> {
    /// Check whether `needle` is outside and left of `self`.
    pub fn left_outside<I: SumInfo, PI: PathInfo<I>>(self, needle: &PI) -> bool
        where PS: SubOrd<PI>,
    {
        match self.left.sub_cmp(needle) {
            Ordering::Greater => true, // self.left > needle
            _ => false,
        }
    }

    /// Check whether `needle` is outside and right of `self`.
    pub fn right_outside<I: SumInfo, PI: PathInfo<I>>(self, needle: &PI) -> bool
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

/// **Panics** if the iterator is empty.
impl<L: Leaf, NP: NodesPtr<L>> FromIterator<L> for Node<L, NP> {
    fn from_iter<I: IntoIterator<Item=L>>(iter: I) -> Self {
        enum IterStatus<L: Leaf, NP: NodesPtr<L>> {
            More(Node<L, NP>),
            Done(Node<L, NP>),
            Empty,
        }

        fn __base<L, NP, I>(iter: &mut I) -> IterStatus<L, NP>
            where L: Leaf, NP: NodesPtr<L>, I: Iterator<Item=L>,
        {
            if let Some(mut leaf_prev) = iter.next() {
                let mut nodes = ArrayVec::new();
                let done = loop {
                    if let Some(leaf) = iter.next() {
                        if let Some(leaf_split) = leaf_prev.merge_maybe_split(leaf) {
                            nodes.push(Node::from_leaf(leaf_prev));
                            leaf_prev = leaf_split;
                        }

                        if nodes.len() == NP::max_size() - 1 {
                            break false;
                        }
                    } else {
                        break true;
                    }
                };
                nodes.push(Node::from_leaf(leaf_prev));
                let node = Node::from_children(NP::new(nodes));
                if done {
                    IterStatus::Done(node)
                } else {
                    IterStatus::More(node)
                }
            } else {
                IterStatus::Empty
            }
        }

        fn __take<L, NP, I>(height: usize, iter: &mut I) -> IterStatus<L, NP>
            where L: Leaf, NP: NodesPtr<L>, I: Iterator<Item=L>,
        {
            debug_assert!(height > 0);
            if height == 1 {
                __base(iter)
            } else {
                match __take(height - 1, iter) {
                    IterStatus::More(node) => __grow(node, iter),
                    status => status,
                }
            }
        }

        fn __grow<L, NP, I>(node: Node<L, NP>, iter: &mut I) -> IterStatus<L, NP>
            where L: Leaf, NP: NodesPtr<L>, I: Iterator<Item=L>,
        {
            debug_assert!(node.has_min_size());
            let height = node.height();
            debug_assert!(height > 0);
            let mut nodes: ArrayVec<NP::Array> = ArrayVec::new();
            nodes.push(node);
            let done = loop {
                debug_assert!(nodes.len() < NP::max_size());
                match __take(height, iter) {
                    IterStatus::More(node) => {
                        debug_assert_eq!(node.height(), height);
                        debug_assert!(node.has_min_size());
                        nodes.push(node);
                        if nodes.len() == NP::max_size() {
                            break false;
                        }
                    }
                    IterStatus::Done(node) => {
                        let last_node = nodes.pop().unwrap();
                        match Node::maybe_concat(last_node, node) {
                            (node1, Some(node2)) => {
                                nodes.push(node1);
                                nodes.push(node2);
                            }
                            (node1, None) => {
                                nodes.push(node1);
                            }
                        }
                        break true;
                    }
                    IterStatus::Empty => {
                        break true;
                    }
                }
            };
            let node = Node::from_children(NP::new(nodes));
            if done {
                IterStatus::Done(node)
            } else {
                IterStatus::More(node)
            }
        }

        let mut iter = iter.into_iter();
        let mut status = __base(&mut iter);
        loop {
            match status {
                IterStatus::More(node) => status = __grow(node, &mut iter),
                IterStatus::Done(node) => break node,
                IterStatus::Empty => panic!("Empty iterator!"),
            }
        }
    }
}

fn balanced_split<L: Leaf, NP: NodesPtr<L>>(total: usize) -> (usize, usize) {
    debug_assert!(NP::max_size() <= total && total <= 2*NP::max_size());
    // Make left heavy. Splitting at midpoint is another option
    let n_left = cmp::min(total - NP::max_size()/2, NP::max_size());
    let n_right = total - n_left;
    debug_assert!(NP::max_size()/2 <= n_left && n_left <= NP::max_size());
    debug_assert!(NP::max_size()/2 <= n_right && n_right <= NP::max_size());
    (n_left, n_right)
}

// Tries to merge two lists of nodes into one (returns true), otherwise balances the lists so that
// both of them have at least NP::max_size()/2 nodes (returns false).
//
// It is best to avoid a direct call to this in favor of InternalVal::extend_maybe_balance
fn balance_maybe_merge<L: Leaf, NP: NodesPtr<L>>(
    children1: &mut ArrayVec<NP::Array>, children2: &mut ArrayVec<NP::Array>
) -> bool {
    let (len1, len2) = (children1.len(), children2.len());
    if len1 + len2 <= NP::max_size() {
        children1.extend(children2.drain(..));
        debug_assert_eq!(children1.len(), len1 + len2);
        true
    } else if len1 < NP::max_size()/2 || len2 < NP::max_size()/2 {
        let (newlen1, newlen2) = balanced_split::<L, NP>(len1 + len2);
        if len1 > len2 {
            let mut tmp_children2 = ArrayVec::<NP::Array>::new();
            tmp_children2.extend(children1.drain(newlen1..));
            tmp_children2.extend(children2.drain(..));
            mem::swap(children2, &mut tmp_children2);
        } else {
            let drain2 = len2 - newlen2;
            children1.extend(children2.drain(..drain2));
        }
        debug_assert_eq!(children1.len() + children2.len(), len1 + len2);
        false
    } else {
        false
    }
}

// Inserts newnode into the list of nodes at the specified position. If the list overflows, splits
// the list into two and returns a new node created from right half of the split.
pub(crate) fn insert_maybe_split<L: Leaf, NP: NodesPtr<L>>(
    nodes: &mut ArrayVec<NP::Array>,
    idx: usize,
    newnode: Node<L, NP>
) -> Option<NP> {
    debug_assert!(newnode.has_min_size());

    if nodes.len() < NP::max_size() {
        nodes.insert(idx, newnode);
        None
    } else {
        let extra;
        if idx == 16 {
            extra = newnode;
        } else {
            debug_assert!(idx < 16);
            extra = nodes.pop().unwrap();
            nodes.insert(idx, newnode);
        }
        let n_left = balanced_split::<L, NP>(NP::max_size() + 1).0;
        let mut right: ArrayVec<_> = nodes.drain(n_left..).collect();
        right.push(extra);
        Some(NP::new(right))
    }
}

impl<L: Leaf> LeafVal<L> {
    pub(crate) fn from_value(leaf: L) -> Self {
        LeafVal {
            info: leaf.compute_info(),
            val: leaf,
        }
    }

    pub(crate) fn merge_maybe_split(&mut self, other: Self) -> Option<Self> {
        let maybe_split = self.val.merge_maybe_split(other.val).map(LeafVal::from_value);
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

impl<L: Leaf, NP: NodesPtr<L>> InternalVal<L, NP> {
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
        InternalVal { info, height, nodes }
    }

    // Returns whether `self` was merged with `other`. If `true`, `other` will have zero children
    // and must not be used any further.
    pub(crate) fn try_merge_with(&mut self, other: &mut Self) -> bool {
        debug_assert_eq!(self.height, other.height);
        let merged_info = self.info.gather(other.info);
        let merged = {
            let children_self = NP::make_mut(&mut self.nodes);
            let children_other = NP::make_mut(&mut other.nodes);
            balance_maybe_merge::<L, NP>(children_self, children_other)
        };
        if merged {
            self.info = merged_info;
        } else {
            self.info = Self::summarize(&self.nodes).0;
            other.info = Self::summarize(&other.nodes).0;
        }
        merged
    }
}

impl<L: Leaf, NP: NodesPtr<L>> Node<L, NP> {
    pub(crate) fn internal_mut_must(&mut self) -> &mut InternalVal<L, NP> {
        match *self {
            Node::Internal(ref mut int) => int,
            Node::Leaf(_) => unreachable!("buggy internal_mut_must call"),
        }
    }

    pub(crate) fn into_leaf_must(self) -> L {
        match self.into_leaf() {
            Ok(leaf) => leaf,
            Err(_) => unreachable!("buggy into_leaf_must call"),
        }
    }

    pub(crate) fn into_children_must(self) -> NP {
        match self.into_children() {
            Ok(nodes) => nodes,
            Err(_) => unreachable!("buggy into_children_must call"),
        }
    }

    pub(crate) fn has_min_size(&self) -> bool {
        match *self {
            Node::Internal(ref int) => int.nodes.len() >= NP::max_size()/2,
            Node::Leaf(LeafVal { ref val, .. }) => val.has_min_size(),
        }
    }

    pub(crate) fn join_two(node1: Node<L, NP>, node2: Node<L, NP>) -> Node<L, NP> {
        debug_assert_eq!(node1.height(), node2.height());
        debug_assert!(node1.has_min_size() && node2.has_min_size());
        let mut nodes = ArrayVec::new();
        nodes.push(node1);
        nodes.push(node2);
        Node::from_children(NP::new(nodes))
    }

    pub(crate) fn merge_maybe_split(&mut self, other: Self) -> Option<Self> {
        use self::Node::{Leaf, Internal};
        match *self {
            Leaf(ref mut self_leaf_val) => {
                if let Leaf(other_leaf_val) = other {
                    self_leaf_val.merge_maybe_split(other_leaf_val).map(|olv| Node::Leaf(olv))
                } else {
                    unreachable!()
                }
            }
            Internal(ref mut self_int) => {
                if let Internal(mut other_int) = other {
                    if self_int.try_merge_with(&mut other_int) {
                        None
                    } else {
                        Some(Internal(other_int))
                    }
                } else {
                    unreachable!()
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ::test_help::*;

    #[test]
    fn iter() {
        let total = 768;
        let node: NodeRc<_> = (0..total).map(|i| ListLeaf(i + 1)).collect();
        assert_eq!(node.info(), ListInfo { count: total, sum: total*(total + 1)/2 });
    }

    #[test]
    fn info_height() {
        let mut node = NodeRc::from_leaf(ListLeaf(1));
        assert_eq!(node.info(), ListInfo { count: 1, sum: 1 });
        assert_eq!(node.height(), 0);
        for i in 2..17 {
            node = NodeRc::concat(node, NodeRc::from_leaf(ListLeaf(i)));
            assert_eq!(node.info(), ListInfo { count: i, sum: i * (i+1) / 2 });
            assert_eq!(node.height(), 1);
        }
        node = NodeRc::concat(node, NodeRc::from_leaf(ListLeaf(17)));
        assert_eq!(node.info(), ListInfo { count: 17, sum: 17 * 18 / 2 });
        assert_eq!(node.height(), 2);
    }

    #[test]
    fn concat() {
        use super::{NodesPtr, Rc16};
        let mut node = NodeRc::from_leaf(ListLeaf(0));
        let nodes = (1..17).map(|i| NodeRc::from_leaf(ListLeaf(i))).collect();
        node = NodeRc::concat(node, NodeRc::from_children(Rc16::new(nodes)));
        assert_eq!(node.height(), 2);

        let children = node.children();
        assert_eq!(children.len(), 2);
        for child_node in children {
            assert!(child_node.children().len() >= 8);
        }
    }

    #[test]
    fn path_get() {
        let mut node = NodeRc::from_leaf(ListLeaf(0));
        for i in 1..16 {
            node = NodeRc::concat(node, NodeRc::from_leaf(ListLeaf(i)));
        }
        let mut sums = Vec::new();
        for i in 0..16 {
            println!("{}", i);
            let mut hit = 0;
            node.visit_subseq::<ListPath, _, _>(ListIndex(i+1), ListIndex(i+1), |leaf_ref| {
                assert_eq!(leaf_ref.leaf, &ListLeaf(i));
                assert_eq!(leaf_ref.info, ListInfo { count: 1, sum: i });
                assert_eq!(leaf_ref.before, ListPath { index: i, run: i.wrapping_sub(1)*i/2 });
                assert_eq!(leaf_ref.after, ListPath { index: i + 1, run: i*(i+1)/2 });
                sums.push(leaf_ref.after.run);
                hit += 1;
            });
            assert_eq!(hit, 1);
        }
        let mut sum_hits = 0;
        for i in 0..(15*16/2 + 1) {
            let mut hit = 0;
            node.visit_subseq::<ListRun, _, _>(ListRun(i), ListRun(i+1), |leaf_ref| {
                let val = leaf_ref.leaf.0;
                println!("{}, val: {}", i, val);
                assert_eq!(leaf_ref.info, ListInfo { count: 1, sum: val });
                assert_eq!(leaf_ref.before, ListRun(val.wrapping_sub(1)*val/2));
                assert_eq!(leaf_ref.after, ListRun(val*(val+1)/2));
                assert!(i <= leaf_ref.after.0);
                assert!(leaf_ref.before.0 < i+1);
                hit += 1;
            });
            if let Ok(val) = sums.binary_search(&i) {
                println!("val: {}", val);
                if val < 16-1 {
                    assert_eq!(hit, 2);
                } else {
                    assert_eq!(hit, 1);
                }
                sum_hits += 1;
            } else {
                assert_eq!(hit, 1);
            }
        }
        assert_eq!(sum_hits, 16);
    }

    #[test]
    fn insert() {
        // TODO
    }

    #[test]
    fn remove() {
        // TODO
    }

    // TODO more tests
}
