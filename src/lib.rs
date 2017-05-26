//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! Both design and implementation are heavily based on [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope

extern crate arrayvec;

use std::cmp;
use std::iter::FromIterator;

use arrayvec::ArrayVec;

pub mod cursor;
pub mod cursor_mut;

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
///
/// **Unstable:** Subject to change. `plus` may be renamed, `minus` may be removed.
pub trait Info: Copy {
    /// The operation used for combining two info objects. Should be commutative and associative.
    fn plus(self, other: Self) -> Self;

    /// The inverse of plus such that `x.plus(y).minus(y) == x` for all `x` and `y`.
    ///
    /// Used to optimize certain tree traversal operations.
    fn minus(self, other: Self) -> Self;

    // An alternative:
    //   /// used when gathering info from children to parent nodes. commutative and associative.
    //   fn gather_up(i1: Self, i2: Self) -> Self;
    //
    //   /// used when calculating the cumulative info from the root when traversing down a tree.
    //   fn gather_down(cumulative: Option<Self>, next: Self) -> Self;
    //
    //   /// inverse of `gather_down`. If info on two adjacent nodes are i1 and i2, and c0 is the
    //   /// cumulative info before i1, then the following condition should hold
    //   ///     g(c0,i1) == g_inv( g(g(c0,i1),i2) , i2 , i1 )
    //   fn gather_down_inv(cumulative: Self, cur: Self, prev: Option<Self>) -> Option<Self>;
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
    fn plus(self, _: ()) { }
    #[inline]
    fn minus(self, _: ()) { }
}

impl Info for usize {
    #[inline]
    fn plus(self, other: usize) -> usize {
        self + other
    }
    #[inline]
    fn minus(self, other: usize) -> usize {
        self - other
    }
}

use std::ops::{Deref, DerefMut};

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
            info = info.plus(child.info());
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

    /// Traverse this node conditioned on a callback which is provided with cumulatively gathered
    /// info from left to right. Returns `Err(_)` if called on a leaf or `f` returned all `false`.
    #[inline]
    pub fn gather_traverse<'a, F>(&'a self, start: L::Info, mut f: F) -> TraverseResult<'a, L>
        where F: FnMut(L::Info, L::Info) -> bool
    {
        let mut cur_info = start;
        match self {
            &Node::Internal(ref int) => {
                for (idx, node) in int.nodes.iter().enumerate() {
                    let next_info = cur_info.plus(node.info());
                    if f(cur_info, next_info) {
                        return Ok(TraverseSummary { child: node, info: cur_info, index: idx });
                    }
                    cur_info = next_info;
                }
                Err(TraverseError::AllFalse)
            }
            &Node::Leaf(_) => Err(TraverseError::IsLeaf),
        }
    }

    /// Same as `gather_traverse` but in reverse. The `Info` values passed to `f` will be exactly
    /// the same for corresponding nodes as calling `gather_traverse` with the exact same parameter
    /// `start`.
    #[inline]
    pub fn gather_traverse_rev<'a, F>(&'a self, start: L::Info, mut f: F) -> TraverseResult<'a, L>
        where F: FnMut(L::Info, L::Info) -> bool
    {
        // an alternative implementation without using minus is to calculate all info beforehand
        // into an NVec<L::Info> and zip iterate them with child nodes
        let mut next_info = start.plus(self.info());
        match self {
            &Node::Internal(ref int) => {
                for (idx, node) in int.nodes.iter().enumerate().rev() {
                    let cur_info = next_info.minus(node.info());
                    if f(cur_info, next_info) {
                        return Ok(TraverseSummary { child: node, info: cur_info, index: idx });
                    }
                    next_info = cur_info;
                }
                Err(TraverseError::AllFalse)
            }
            &Node::Leaf(_) => Err(TraverseError::IsLeaf),
        }
    }

    /// Concatenates two nodes of possibly different heights into a single balanced node.
    pub fn concat(node1: Node<L>, node2: Node<L>) -> Node<L> {
        let h1 = node1.height();
        let h2 = node2.height();

        match h1.cmp(&h2) {
            cmp::Ordering::Less => {
                let children2 = node2.children();
                if h1 == h2 - 1 && node1.has_min_size() {
                    Node::merge_nodes(&[node1], children2)
                } else {
                    let newnode = Node::concat(node1, children2[0].clone());
                    if newnode.height() == h2 - 1 {
                        Node::merge_nodes(&[newnode], &children2[1..])
                    } else {
                        debug_assert_eq!(newnode.height(), h2);
                        Node::merge_nodes(newnode.children(), &children2[1..])
                    }
                }
            },
            cmp::Ordering::Equal => {
                if node1.has_min_size() && node2.has_min_size() {
                    Node::merge_two(node1, node2)
                } else {
                    Node::merge_nodes(node1.children(), node2.children())
                }
            },
            cmp::Ordering::Greater => {
                let children1 = node1.children();
                if h2 == h1 - 1 && node2.has_min_size() {
                    Node::merge_nodes(children1, &[node2])
                } else {
                    let lastix = children1.len() - 1;
                    let newnode = Node::concat(children1[lastix].clone(), node2);
                    if newnode.height() == h1 - 1 {
                        Node::merge_nodes(&children1[..lastix], &[newnode])
                    } else {
                        debug_assert_eq!(newnode.height(), h1);
                        Node::merge_nodes(&children1[..lastix], newnode.children())
                    }
                }
            }
        }
    }
}

pub type TraverseResult<'a, L> = Result<TraverseSummary<'a, L>, TraverseError>;

pub struct TraverseSummary<'a, L: Leaf + 'a> {
    child: &'a Node<L>,
    info: L::Info,
    index: usize,
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

    fn merge_nodes(children1: &[Node<L>], children2: &[Node<L>]) -> Node<L> {
        let n_children = children1.len() + children2.len();
        let mut iter = children1.iter().chain(children2).cloned();
        if n_children <= MAX_CHILDREN {
            Node::from_nodes(RC::new(iter.collect()))
        } else {
            debug_assert!(n_children <= 2 * MAX_CHILDREN);
            // Make left heavy. Splitting at midpoint is another option
            let n_left = cmp::min(n_children - MIN_CHILDREN, MAX_CHILDREN);
            let left = Node::from_nodes(RC::new(iter.by_ref().take(n_left).collect()));
            let right = Node::from_nodes(RC::new(iter.collect()));
            Node::merge_two(left, right)
        }
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
