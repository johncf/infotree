//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! Both design and implementation are heavily based on [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope

extern crate arrayvec;

use std::sync::Arc;
use std::cmp;

use arrayvec::ArrayVec;

pub mod cursor;

const MIN_CHILDREN: usize = 8;
const MAX_CHILDREN: usize = 16;

type NVec<T> = ArrayVec<[T; MAX_CHILDREN]>;

/// A self-balancing B-Tree-like data structure.
///
/// UniTree is a self-balancing data structure similar to B-Tree, except that each element in an
/// internal node corresponds to exactly one branch (as opposed to having k elements and k+1
/// branches). Another difference is that data is stored in leaf nodes similar to a B+Tree; but
/// unlike B+Trees, there are no direct links between leaf nodes.
///
/// Note: `UniTree` uses `Arc` for its CoW capability.
#[derive(Clone)]
pub struct UniTree<L: Leaf> {
    pub root: Option<Node<L>>,
}

/// The leaves of a `UniTree` should implement this trait.
///
/// Note: If cloning a leaf is expensive, consider wrapping it in `Arc`.
pub trait Leaf: Clone {
    type Info: Info;

    fn compute_info(&self) -> Self::Info;
}

/// Metadata that need to be accumulated hierarchically over the tree.
pub trait Info: Clone {
    fn accumulate(&mut self, other: &Self);
}

/// A `UniTree` node.
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
    nodes: Arc<NVec<Node<L>>>,
}

#[doc(hidden)]
#[derive(Clone)]
pub struct LeafVal<L: Leaf> {
    info: L::Info,
    val: L,
}

impl Info for () {
    fn accumulate(&mut self, _: &()) { }
}

impl Info for usize {
    fn accumulate(&mut self, other: &usize) {
        *self += *other;
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
    pub fn from_leaf(leaf: L) -> Node<L> {
        Node::Leaf(LeafVal {
                       info: leaf.compute_info(),
                       val: leaf,
                   })
    }

    /// All nodes should be at the same height, panics otherwise.
    pub fn from_nodes(nodes: Arc<NVec<Node<L>>>) -> Node<L> {
        let height = nodes[0].height() + 1;
        let mut info = nodes[0].info().clone();
        for child in &nodes[1..] {
            assert_eq!(height, child.height() + 1);
            info.accumulate(&child.info());
        }
        Node::Internal(InternalVal { info, height, nodes })
    }

    /// Returns the accumulated info for this node.
    pub fn info(&self) -> &L::Info {
        match *self {
            Node::Internal(InternalVal { ref info, .. })
                | Node::Leaf(LeafVal { ref info, .. }) => info,
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

    /// Traverse this node conditioned on a callback which is provided with accumulated info from
    /// left to right. Returns `Err(())` if called on a leaf.
    pub fn accu_info_by<T, F>(&self, start: L::Info, mut f: F) -> Result<Option<T>, ()>
        where F: FnMut(usize, L::Info, Option<L::Info>) -> Option<T>
    {
        let mut cur = start;
        match self {
            &Node::Internal(ref int) => {
                let mut idx = 0;
                for node in &*int.nodes {
                    let mut next = cur.clone();
                    next.accumulate(node.info());
                    if let Some(x) = f(idx, cur, Some(next.clone())) {
                        return Ok(Some(x));
                    }
                    cur = next;
                    idx += 1;
                }
                Ok(f(idx, cur, None))
            }
            &Node::Leaf(_) => Err(()),
        }
    }

    // Returns `(index, accu_info)` of the node at which `f` returned `true`. If all were `false`,
    // this returns `(index, accu_info)` of the last child in the node. Returns `Err` if called on
    // a leaf node.
    fn accu_info_with_default_end<F>(&self, start: L::Info, mut f: F) -> Result<(usize, L::Info), ()>
        where F: FnMut(L::Info, L::Info) -> bool
    {
        let mut info = start;
        self.accu_info_by(info.clone(),
                          |idx, info_beg, info_end| {
                              match info_end {
                                  Some(info_end) => {
                                      info = info_beg.clone();
                                      match f(info_beg, info_end) {
                                          true => Some(idx),
                                          false => None,
                                      }
                                  }
                                  None => Some(idx - 1), // the "default_end"
                              }
                          })
            .map(|idx| (idx.unwrap(), info))
    }

    fn children_raw(&self) -> &Arc<NVec<Node<L>>> {
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
        Node::from_nodes(Arc::new(nodes))
    }

    fn merge_nodes(children1: &[Node<L>], children2: &[Node<L>]) -> Node<L> {
        let n_children = children1.len() + children2.len();
        let mut iter = children1.iter().chain(children2).cloned();
        if n_children <= MAX_CHILDREN {
            Node::from_nodes(Arc::new(iter.collect()))
        } else {
            debug_assert!(n_children <= 2 * MAX_CHILDREN);
            // Make left heavy. Splitting at midpoint is another option
            let n_left = cmp::min(n_children - MIN_CHILDREN, MAX_CHILDREN);
            let left = Node::from_nodes(Arc::new(iter.by_ref().take(n_left).collect()));
            let right = Node::from_nodes(Arc::new(iter.collect()));
            Node::merge_two(left, right)
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

impl<L: Leaf> UniTree<L> {
    pub fn new() -> UniTree<L> {
        UniTree { root: None }
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

impl<L: Leaf> From<Node<L>> for UniTree<L> {
    fn from(node: Node<L>) -> UniTree<L> {
        UniTree { root: Some(node) }
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

    pub fn root_of<L: Leaf>(tree: &UniTree<L>) -> &Node<L> {
        tree.root.as_ref().expect("tree root was empty")
    }

    pub fn info_of<L: Leaf>(tree: &UniTree<L>) -> &L::Info {
        root_of(&tree).info()
    }

    pub fn height_of<L: Leaf>(tree: &UniTree<L>) -> usize {
        root_of(&tree).height()
    }

    #[test]
    fn basics() {
        let mut tree = UniTree::new();
        tree.push_back(Node::from_leaf(TestLeaf(1)));
        assert_eq!(height_of(&tree), 0);
        assert_eq!(*info_of(&tree), 1);
        tree.push_back(Node::from_leaf(TestLeaf(2)));
        assert_eq!(height_of(&tree), 1);
        assert_eq!(*info_of(&tree), 3);
        for i in 3..17 {
            tree.push_back(Node::from_leaf(TestLeaf(i)));
        }
        assert_eq!(height_of(&tree), 1);
        assert_eq!(*info_of(&tree), 8 * 17);
        tree.push_back(Node::from_leaf(TestLeaf(17)));
        assert_eq!(height_of(&tree), 2);
        assert_eq!(*info_of(&tree), 9 * 17);
    }

    // FIXME need more tests
}
