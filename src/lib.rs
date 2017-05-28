//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! Both design and implementation are heavily based on [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope

extern crate arrayvec;

use std::cmp;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use arrayvec::ArrayVec;

pub mod cursor;
pub mod cursor_mut;

pub mod info_ext;

pub use info_ext::PathInfo;
pub use cursor::CursorT;
pub use cursor_mut::CursorMutT;

const MIN_CHILDREN: usize = 8;
const MAX_CHILDREN: usize = 16;

type RC<T> = std::sync::Arc<T>; // replace with std::rc::Rc<T> to get significant speed-up.
type NVec<T> = ArrayVec<[T; MAX_CHILDREN]>;

// Maximum height of tree that can be handled by cursor types.
const CURSOR_MAX_HT: usize = 8;
// => Maximum number of elements = MAX_CHILDREN^CURSOR_P2R_SIZE = 16^8 = 2^32

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;

/// A self-balancing copy-on-write tree data structure.
///
/// All major operations are defined in either the `Node` structure, and the cursor types.
///
/// See [`Node`](struct.InfoTree.html) for more details.
#[derive(Clone)]
pub struct InfoTree<L: Leaf> {
    pub root: Option<Node<L>>,
}

/// The leaves of a `InfoTree` should implement this trait.
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

/// The basic building block of a tree.
///
/// `Node` is similar to a B-Tree node, except that it has the same number of entries and branches
/// (as opposed to k elements and k+1 branches in B-Trees). Another difference is that data is
/// stored only in leaf nodes similar to a B+Tree; but unlike B+Trees, there are no direct links
/// between leaf nodes.
///
/// Note: `Node` uses `Arc` for its CoW capability.
#[derive(Clone)]
pub enum Node<L: Leaf> {
    Internal(InternalVal<L>),
    Leaf(LeafVal<L>),
}

#[doc(hidden)]
#[derive(Clone)]
pub struct InternalVal<L: Leaf> {
    info: L::Info,
    height: usize, // > 0
    nodes: RC<NVec<Node<L>>>,
}

#[doc(hidden)]
#[derive(Clone)]
pub struct LeafVal<L: Leaf> {
    info: L::Info,
    val: L,
}

impl Info for () {
    #[inline]
    fn gather(self, _: ()) { }
}

impl Info for usize {
    #[inline]
    fn gather(self, other: usize) -> usize { self + other }
}

impl<L: Leaf> Node<L> {
    #[inline]
    pub fn from_leaf(leaf: L) -> Node<L> {
        Node::Leaf(LeafVal {
                       info: leaf.compute_info(),
                       val: leaf,
                   })
    }

    /// All nodes should be at the same height, panics otherwise.
    #[inline]
    pub fn from_nodes(nodes: RC<NVec<Node<L>>>) -> Node<L> {
        let height = nodes[0].height() + 1;
        let mut info = nodes[0].info();
        for child in &nodes[1..] {
            assert_eq!(height, child.height() + 1);
            info = info.gather(child.info());
        }
        Node::Internal(InternalVal { info, height, nodes })
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
    pub fn children(&self) -> &[Node<L>] {
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

    /// Get a mutable reference to the leaf value if this is a leaf node, otherwise return `None`.
    pub fn leaf_mut(&mut self) -> Option<LeafMut<L>> {
        match self {
            &mut Node::Internal(_) => None,
            &mut Node::Leaf(ref mut leaf) => Some(LeafMut(leaf)),
        }
    }

    /// Traverse this node conditioned on a callback which is provided with info from each child node
    /// from left to right. Returns `Err(_)` if called on a leaf or `f` returned all `false`.
    ///
    /// The three arguments to `f` are respectively: child node info, zero-based position from
    /// left, and the remaining number of children (total - position - 1).
    #[inline]
    pub fn traverse<F>(&self, mut f: F) -> Result<(usize, &Node<L>), TraverseError>
        where F: FnMut(L::Info, usize, usize) -> bool
    {
        match self {
            &Node::Internal(ref int) => {
                let n_children = int.nodes.len();
                for (idx, node) in int.nodes.iter().enumerate() {
                    if f(node.info(), idx, n_children - idx - 1) {
                        return Ok((idx, node));
                    }
                }
                Err(TraverseError::AllFalse)
            }
            &Node::Leaf(_) => Err(TraverseError::IsLeaf),
        }
    }

    /// Same as `traverse` but in reverse order.
    #[inline]
    pub fn traverse_rev<F>(&self, mut f: F) -> Result<(usize, &Node<L>), TraverseError>
        where F: FnMut(L::Info, usize, usize) -> bool
    {
        match self {
            &Node::Internal(ref int) => {
                let n_children = int.nodes.len();
                for (idx, node) in int.nodes.iter().enumerate().rev() {
                    if f(node.info(), idx, n_children - idx - 1) {
                        return Ok((idx, node));
                    }
                }
                Err(TraverseError::AllFalse)
            }
            &Node::Leaf(_) => Err(TraverseError::IsLeaf),
        }
    }

    /// Similar to `traverse` with an extra argument for `f` which starts with `first`, and for
    /// each child, `PathInfo::extend`-s it with the child's info.
    pub fn path_traverse<P, F>(&self, first: P, mut f: F) -> Result<(usize, P, &Node<L>), TraverseError>
        where P: PathInfo<L::Info>,
              F: FnMut(P, L::Info, usize, usize) -> bool
    {
        let mut path_info = first;
        self.traverse(|node_info, pos, rem| {
            if f(path_info, node_info, pos, rem) { true }
            else {
                path_info = path_info.extend(node_info);
                false
            }
        }).map(|(idx, child)| (idx, path_info, child))
    }

    /// Same as `path_traverse` but in reverse order. (`first` is initially extended with this
    /// node's info, and for each child, `PathInfo::extend_inv`-s it with child's info. Thus `f`
    /// will be called with `first` at the end, if `extend_inv` is correctly implemented.)
    pub fn path_traverse_rev<P, F>(&self, first: P, mut f: F) -> Result<(usize, P, &Node<L>), TraverseError>
        where P: PathInfo<L::Info>,
              F: FnMut(P, L::Info, usize, usize) -> bool
    {
        let mut path_info = first.extend(self.info());
        self.traverse_rev(|node_info, pos, rem| {
            path_info = path_info.extend_inv(node_info);
            f(path_info, node_info, pos, rem)
        }).map(|(idx, child)| (idx, path_info, child))
    }

    /// Concatenates two nodes of possibly different heights into a single balanced node.
    pub fn concat(node1: Node<L>, node2: Node<L>) -> Node<L> {
        let (node1, maybe_node2) = Node::maybe_concat(node1, node2);
        if let Some(node2) = maybe_node2 {
            Node::merge_two(node1, node2)
        } else {
            node1
        }
    }

    /// Concatenates two nodes of possibly different heights into a single balanced node if the
    /// resulting height does not exceed the maximum height among the original nodes. Otherwise,
    /// splits them into two nodes of the same height.
    pub fn maybe_concat(node1: Node<L>, node2: Node<L>) -> (Node<L>, Option<Node<L>>) {
        // This is an optimized version of the following code:
        // https://github.com/google/xi-editor/blob/cbec578/rust/rope/src/tree.rs#L276-L318
        // The originally adapted code (around 3x slower) is probably much easier to read and
        // understand. It may be found in commit ca3344c (line 222) of this file.

        let h1 = node1.height();
        let h2 = node2.height();

        match h1.cmp(&h2) {
            cmp::Ordering::Less => {
                let mut children2 = node2.into_children_raw();
                let maybe_newnode = {
                    let children2 = RC::make_mut(&mut children2);
                    if h1 == h2 - 1 && node1.has_min_size() {
                        insert_maybe_split(children2, 0, node1)
                    } else {
                        let newnode = Node::concat(node1, children2.remove(0).unwrap());
                        if newnode.height() == h2 - 1 {
                            insert_maybe_split(children2, 0, newnode)
                        } else {
                            debug_assert_eq!(newnode.height(), h2);
                            let mut newchildren = newnode.into_children_raw();
                            if {
                                let newchildren = RC::make_mut(&mut newchildren);
                                std::mem::swap(newchildren, children2);
                                balance_maybe_merge(children2, newchildren)
                            } { // merged into children2
                                None
                            } else {
                                Some(Node::from_nodes(newchildren))
                            }
                        }
                    }
                };
                (Node::from_nodes(children2), maybe_newnode)
            },
            cmp::Ordering::Equal => {
                if node1.has_min_size() && node2.has_min_size() {
                    (node1, Some(node2))
                } else {
                    let mut children1 = node1.into_children_raw();
                    let mut children2 = node2.into_children_raw();
                    if balance_maybe_merge(RC::make_mut(&mut children1), RC::make_mut(&mut children2)) {
                        (Node::from_nodes(children1), None)
                    } else {
                        (Node::from_nodes(children1), Some(Node::from_nodes(children2)))
                    }
                }
            },
            cmp::Ordering::Greater => {
                let mut children1 = node1.into_children_raw();
                let maybe_newnode = {
                    let len1 = children1.len();
                    let children1 = RC::make_mut(&mut children1);
                    if h2 == h1 - 1 && node2.has_min_size() {
                        insert_maybe_split(children1, len1, node2)
                    } else {
                        let newnode = Node::concat(children1.pop().unwrap(), node2);
                        let len1 = len1 - 1;
                        if newnode.height() == h1 - 1 {
                            insert_maybe_split(children1, len1, newnode)
                        } else {
                            debug_assert_eq!(newnode.height(), h1);
                            let mut newchildren = newnode.into_children_raw();
                            if {
                                let newchildren = RC::make_mut(&mut newchildren);
                                balance_maybe_merge(children1, newchildren)
                            } {
                                None
                            } else {
                                Some(Node::from_nodes(newchildren))
                            }
                        }
                    }
                };
                (Node::from_nodes(children1), maybe_newnode)
            }
        }
    }
}

// Tries to merge two lists of nodes into one (returns true), otherwise balances the lists so that
// both of them have at least MIN_CHILDREN nodes (returns false).
fn balance_maybe_merge<L: Leaf>(
    children1: &mut NVec<Node<L>>, children2: &mut NVec<Node<L>>
) -> bool {
    let (len1, len2) = (children1.len(), children2.len());
    if len1 + len2 <= MAX_CHILDREN {
        children1.extend(children2.drain(..));
        true
    } else if len1 < MIN_CHILDREN || len2 < MIN_CHILDREN {
        let (newlen1, newlen2) = balanced_split(len1 + len2);
        if len1 > len2 {
            let mut tmp_children2 = NVec::new();
            tmp_children2.extend(children1.drain(newlen1..));
            tmp_children2.extend(children2.drain(..));
            std::mem::swap(children2, &mut tmp_children2);
        } else {
            let drain2 = len2 - newlen2;
            children1.extend(children2.drain(..drain2));
        }
        false
    } else {
        false
    }
}

// Inserts newnode into the list of nodes at the specified position. If the list overflows, splits
// the list into two and returns a new node created from right half of the split.
fn insert_maybe_split<L: Leaf>(
    nodes: &mut NVec<Node<L>>,
    idx: usize,
    newnode: Node<L>
) -> Option<Node<L>> {
    if nodes.len() < MAX_CHILDREN {
        let res = nodes.insert(idx, newnode);
        debug_assert!(res.is_none());
        None
    } else {
        let extra = nodes.insert(idx, newnode).unwrap(); // like unwrap_err
        let n_left = balanced_split(MAX_CHILDREN + 1).0;
        let mut after: NVec<_> = nodes.drain(n_left + 1..).collect();
        let res = after.push(extra);
        debug_assert!(res.is_none());
        Some(Node::from_nodes(RC::new(after)))
    }
}

/// A wrapper type for a mutably borrowed leaf from a `Node`.
///
/// When `LeafMut` gets dropped, it will update the `Node` to reflect changes in info.
pub struct LeafMut<'a, L: 'a + Leaf>(&'a mut LeafVal<L>);

impl<'a, L: Leaf> Deref for LeafMut<'a, L> {
    type Target = L;

    fn deref(&self) -> &L {
        &self.0.val
    }
}

impl<'a, L: Leaf> DerefMut for LeafMut<'a, L> {
    fn deref_mut(&mut self) -> &mut L {
        &mut self.0.val
    }
}

impl<'a, L: Leaf> Drop for LeafMut<'a, L> {
    fn drop(&mut self) {
        self.0.info = self.0.val.compute_info();
    }
}

pub enum TraverseError {
    AllFalse,
    IsLeaf,
}

impl<L: Leaf> Node<L> {
    fn children_raw(&self) -> &RC<NVec<Node<L>>> {
        match *self {
            Node::Internal(ref int) => &int.nodes,
            Node::Leaf(_) => panic!("children_raw called on a leaf."),
        }
    }

    fn into_children_raw(self) -> RC<NVec<Node<L>>> {
        match self {
            Node::Internal(int) => int.nodes,
            Node::Leaf(_) => panic!("into_children_raw called on a leaf."),
        }
    }

    fn has_min_size(&self) -> bool {
        match *self {
            Node::Internal(ref int) => int.nodes.len() >= MIN_CHILDREN,
            Node::Leaf(_) => true,
        }
    }

    fn merge_two(node1: Node<L>, node2: Node<L>) -> Node<L> {
        let mut nodes = NVec::new();
        nodes.push(node1);
        nodes.push(node2);
        Node::from_nodes(RC::new(nodes))
    }
}

impl<L: Leaf> InfoTree<L> {
    pub fn new() -> InfoTree<L> {
        InfoTree { root: None }
    }

    pub fn push_back(&mut self, node: Node<L>) {
        let root = match self.root.take() {
            Some(root) => Node::concat(root, node),
            None => node,
        };
        self.root = Some(root);
    }

    pub fn push_front(&mut self, node: Node<L>) {
        let root = match self.root.take() {
            Some(root) => Node::concat(node, root),
            None => node,
        };
        self.root = Some(root);
    }
}

impl<L: Leaf> From<Node<L>> for InfoTree<L> {
    fn from(node: Node<L>) -> InfoTree<L> {
        InfoTree { root: Some(node) }
    }
}

impl<L: Leaf> FromIterator<L> for InfoTree<L> {
    fn from_iter<I: IntoIterator<Item=L>>(iter: I) -> Self {
        let mut tree = InfoTree::new();
        let mut iter = iter.into_iter().map(|e| Node::from_leaf(e));

        loop {
            let nodes: NVec<_> = iter.by_ref().take(MAX_CHILDREN).collect();
            if nodes.len() > 0 {
                tree.push_back(Node::from_nodes(RC::new(nodes)));
            } else {
                break;
            }
        }
        tree
    }
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
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct TestLeaf(pub usize);

    impl Leaf for TestLeaf {
        type Info = usize;
        fn compute_info(&self) -> usize {
            self.0
        }
    }

    pub fn root_of<L: Leaf>(tree: &InfoTree<L>) -> &Node<L> {
        tree.root.as_ref().expect("tree root was empty")
    }

    pub fn info_of<L: Leaf>(tree: &InfoTree<L>) -> L::Info {
        root_of(&tree).info()
    }

    pub fn height_of<L: Leaf>(tree: &InfoTree<L>) -> usize {
        root_of(&tree).height()
    }

    #[test]
    fn basics() {
        let mut tree = InfoTree::new();
        tree.push_back(Node::from_leaf(TestLeaf(1)));
        assert_eq!(height_of(&tree), 0);
        assert_eq!(info_of(&tree), 1);
        tree.push_back(Node::from_leaf(TestLeaf(2)));
        assert_eq!(height_of(&tree), 1);
        assert_eq!(info_of(&tree), 3);
        for i in 3..17 {
            tree.push_back(Node::from_leaf(TestLeaf(i)));
        }
        assert_eq!(height_of(&tree), 1);
        assert_eq!(info_of(&tree), 8 * 17);
        tree.push_back(Node::from_leaf(TestLeaf(17)));
        assert_eq!(height_of(&tree), 2);
        assert_eq!(info_of(&tree), 9 * 17);
    }

    // FIXME need more tests
}
