use traits::{Info, Leaf};

use arrayvec::ArrayVec;
use mines::boom;

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
    #[doc(hidden)]
    Never(NeverVal), // only for use with CursorMut
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

#[doc(hidden)]
#[derive(Clone)]
pub struct NeverVal(());

impl<L: Leaf, NP: NodesPtr<L>> Node<L, NP> {
    #[inline]
    pub fn from_leaf(leaf: L) -> Node<L, NP> {
        Node::Leaf(LeafVal {
                       info: leaf.compute_info(),
                       val: leaf,
                   })
    }

    /// All nodes should be at the same height, panics otherwise.
    #[inline]
    pub fn from_children(nodes: NP) -> Node<L, NP> {
        Node::Internal(InternalVal::from_children(nodes))
    }

    /// Tries to unwrap the node into leaf. If node is internal, `Err(self)` is returned.
    pub fn into_leaf(self) -> Result<L, Node<L, NP>> {
        match self {
            Node::Internal(_) => Err(self),
            Node::Leaf(LeafVal { val, .. }) => Ok(val),
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    /// Tries to unwrap the node into its children. If node is leaf, `Err(self)` is returned.
    pub fn into_children(self) -> Result<NP, Node<L, NP>> {
        match self {
            Node::Internal(InternalVal { nodes, .. }) => Ok(nodes),
            Node::Leaf(_) => Err(self),
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    /// Returns the info for this node, gathered from all its leaves.
    pub fn info(&self) -> L::Info {
        match *self {
            Node::Internal(InternalVal { info, .. })
                | Node::Leaf(LeafVal { info, .. }) => info,
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    pub fn height(&self) -> usize {
        match *self {
            Node::Internal(ref int) => int.height,
            Node::Leaf(_) => 0,
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    pub fn is_leaf(&self) -> bool {
        match *self {
            Node::Internal(_) => false,
            Node::Leaf(_) => true,
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    /// Get the child nodes of this node. If this is a leaf node, this will return an empty slice.
    ///
    /// Note that internal nodes always contain at least one child node.
    pub fn children(&self) -> &[Node<L, NP>] {
        match *self {
            Node::Internal(ref int) => &*int.nodes,
            Node::Leaf(_) => &[],
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    /// Get the leaf value if this is a leaf node, otherwise return `None`.
    pub fn leaf(&self) -> Option<&L> {
        match *self {
            Node::Internal(_) => None,
            Node::Leaf(ref leaf) => Some(&leaf.val),
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    /// Concatenates two nodes of possibly different heights into a single balanced node.
    pub fn concat(node1: Node<L, NP>, node2: Node<L, NP>) -> Node<L, NP> {
        let (node1, maybe_node2) = Node::maybe_concat(node1, node2);
        if let Some(node2) = maybe_node2 {
            Node::merge_two(node1, node2)
        } else {
            node1
        }
    }

    /// Concatenates two nodes of possibly different heights into a single balanced node if the
    /// resulting height does not exceed the maximum height among the original nodes. Otherwise,
    /// splits them into two nodes of equal height.
    pub fn maybe_concat(mut node1: Node<L, NP>, mut node2: Node<L, NP>) -> (Node<L, NP>, Option<Node<L, NP>>) {
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
                            .map(|split_children| Node::from_children(split_children))
                    } else {
                        let newnode2 = Node::concat(node1, children2.remove(0).unwrap());
                        if newnode2.height() == h2 - 1 {
                            insert_maybe_split(children2, 0, newnode2)
                                .map(|split_children| Node::from_children(split_children))
                        } else {
                            debug_assert_eq!(newnode2.height(), h2);
                            let mut newchildren = newnode2.into_children_must();
                            let merged = {
                                let newchildren = NP::make_mut(&mut newchildren);
                                mem::swap(newchildren, children2);
                                balance_maybe_merge::<_, NP>(children2, newchildren)
                            };
                            if merged {
                                None
                            } else {
                                Some(Node::from_children(newchildren))
                            }
                        }
                    }
                };
                (Node::from_children(children2), maybe_newnode)
            },
            Ordering::Equal => {
                if node1.has_min_size() && node2.has_min_size() {
                    (node1, Some(node2))
                } else {
                    if node1.internal_mut_must().try_merge_with(node2.internal_mut_must()) {
                        (node1, None)
                    } else {
                        (node1, Some(node2))
                    }
                }
            },
            Ordering::Greater => {
                let mut children1 = node1.into_children_must();
                let maybe_newnode = {
                    let len1 = children1.len();
                    let children1 = NP::make_mut(&mut children1);
                    if h2 == h1 - 1 && node2.has_min_size() {
                        insert_maybe_split(children1, len1, node2)
                            .map(|split_children| Node::from_children(split_children))
                    } else {
                        let newnode1 = Node::concat(children1.pop().unwrap(), node2);
                        let len1 = len1 - 1;
                        if newnode1.height() == h1 - 1 {
                            insert_maybe_split(children1, len1, newnode1)
                                .map(|split_children| Node::from_children(split_children))
                        } else {
                            debug_assert_eq!(newnode1.height(), h1);
                            let mut newchildren = newnode1.into_children_must();
                            let merged = {
                                let newchildren = NP::make_mut(&mut newchildren);
                                balance_maybe_merge::<_, NP>(children1, newchildren)
                            };
                            if merged {
                                None
                            } else {
                                Some(Node::from_children(newchildren))
                            }
                        }
                    }
                };
                (Node::from_children(children1), maybe_newnode)
            }
        }
    }
}

/// This implementation is for testing and benchmarking purposes. This panics if the iterator is
/// empty. Use `CursorMut::collect` which not only avoids panicking, but is also more efficient.
impl<L: Leaf, NP: NodesPtr<L>> FromIterator<L> for Node<L, NP> {
    fn from_iter<I: IntoIterator<Item=L>>(iter: I) -> Self {
        let mut iter = iter.into_iter().map(Node::from_leaf);
        let mut root = iter.next().expect("Iterator should not be empty.");

        loop {
            let nodes: ArrayVec<_> = iter.by_ref().take(NP::max_size()).collect();
            if nodes.len() > 0 {
                let node = Node::from_children(NP::new(nodes));
                root = Node::concat(root, node);
            } else {
                break;
            }
        }
        root
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
        let _res = nodes.insert(idx, newnode);
        debug_assert!(_res.is_none());
        None
    } else {
        let extra = nodes.insert(idx, newnode).unwrap(); // like unwrap_err
        let n_left = balanced_split::<L, NP>(NP::max_size() + 1).0;
        let mut right: ArrayVec<_> = nodes.drain(n_left..).collect();
        let _res = right.push(extra);
        debug_assert!(_res.is_none());
        Some(NP::new(right))
    }
}

pub enum TraverseError {
    AllFalse,
    IsLeaf,
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

    pub(crate) fn from_children(nodes: NP) -> Self {
        let (info, height) = Self::summarize(&nodes);
        InternalVal { info, height, nodes }
    }

    pub(crate) fn info(&self) -> L::Info {
        self.info
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
    // Update leaf value in place.
    pub(crate) fn leaf_update<F>(&mut self, f: F) where F: FnOnce(&mut L) {
        if let Node::Leaf(ref mut leaf) = *self {
            f(&mut leaf.val);
            leaf.info = leaf.val.compute_info();
        }
    }

    pub(crate) fn internal_mut_must(&mut self) -> &mut InternalVal<L, NP> {
        match *self {
            Node::Internal(ref mut int) => int,
            Node::Leaf(_) => unreachable!("buggy internal_mut_must call"),
            Node::Never(_) => unsafe { boom("Never!") },
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
            Node::Leaf(_) => true,
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    pub(crate) fn never_take(&mut self) -> Node<L, NP> {
        let node = mem::replace(self, Node::never());
        debug_assert!(!node.is_never());
        node
    }

    // Swaps `self` with `node`. Exactly one of the nodes being swapped must be a never node.
    pub(crate) fn never_swap(&mut self, other: &mut Node<L, NP>) {
        debug_assert_eq!(self.is_never(), !other.is_never());
        mem::swap(self, other);
    }

    pub(crate) fn merge_two(node1: Node<L, NP>, node2: Node<L, NP>) -> Node<L, NP> {
        let mut nodes = ArrayVec::new();
        nodes.push(node1);
        nodes.push(node2);
        Node::from_children(NP::new(nodes))
    }

    pub(crate) fn never() -> Node<L, NP> {
        Node::Never(NeverVal(()))
    }

    // only do debug_assert with this function
    pub(crate) fn is_never(&self) -> bool {
        match *self {
            Node::Never(_) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use ::test_help::*;

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

    // TODO more tests
}
