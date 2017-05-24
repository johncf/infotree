//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! Both design and implementation are heavily based on [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope

extern crate arrayvec;

use std::sync::Arc;
use std::cmp;

use arrayvec::ArrayVec;

const MIN_CHILDREN: usize = 8;
const MAX_CHILDREN: usize = 16;

type AVec<T> = ArrayVec<[T; MAX_CHILDREN]>;

/// The main B-Tree-like data structure.
///
/// Note: `LeftTree` uses `Arc` for its CoW capability.
#[derive(Clone)]
pub struct LeftTree<I: Info, L: Leaf<I=I>> {
    pub root: Option<Node<I, L>>,
}

/// The metadata that needs to be accumulated hierarchically over the tree.
pub trait Info: Clone {
    fn accumulate(&mut self, other: &Self);
}

/// The leaves of a `LeftTree` should implement this trait.
///
/// Note: If cloning a leaf is expensive, consider wrapping it in `Arc`.
pub trait Leaf: Clone {
    type I: Info;

    fn compute_info(&self) -> Self::I;
}

#[derive(Clone)]
pub enum Node<I: Info, L: Leaf<I=I>> {
    Internal(InternalVal<I, L>),
    Leaf(LeafVal<I, L>),
}

#[derive(Clone)]
pub struct InternalVal<I: Info, L: Leaf<I=I>> {
    info: I,
    height: usize, // > 0
    val: Arc<AVec<Node<I, L>>>,
}

#[derive(Clone)]
pub struct LeafVal<I: Info, L: Leaf<I=I>> {
    info: I,
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

impl<I: Info, L: Leaf<I=I>> Node<I, L> {
    pub fn from_leaf(leaf: L) -> Node<I, L> {
        Node::Leaf(LeafVal {
            info: leaf.compute_info(),
            val: leaf,
        })
    }

    /// All nodes should be at the same height, panics otherwise.
    pub fn from_nodes(nodes: AVec<Node<I, L>>) -> Node<I, L> {
        let height = nodes[0].height() + 1;
        let mut info = nodes[0].info().clone();
        for child in &nodes[1..] {
            assert_eq!(height, child.height() + 1);
            info.accumulate(&child.info());
        }
        Node::Internal(InternalVal {
            info: info,
            height: height,
            val: Arc::new(nodes),
        })
    }

    /// Returns the accumulated info for this node.
    pub fn info(&self) -> &I {
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

    pub fn get_children(&self) -> &[Node<I, L>] {
        match *self {
            Node::Internal(ref int) => &*int.val,
            Node::Leaf(_) => panic!("get_children called on a leaf node"),
        }
    }

    /// For an `Internal` node, this returns whether the number of nodes is `>= 8`. For a `Leaf`
    /// node, this always returns `true`.
    pub fn has_min_size(&self) -> bool {
        match *self {
            Node::Internal(ref int) => int.val.len() >= MIN_CHILDREN,
            Node::Leaf(_) => true,
        }
    }

    fn merge_two(node1: Node<I, L>, node2: Node<I, L>) -> Node<I, L> {
        let mut nodes = AVec::new();
        nodes.push(node1);
        nodes.push(node2);
        Node::from_nodes(nodes)
    }

    fn merge_nodes(children1: &[Node<I, L>], children2: &[Node<I, L>]) -> Node<I, L> {
        let n_children = children1.len() + children2.len();
        let mut iter = children1.iter().chain(children2).cloned();
        if n_children <= MAX_CHILDREN {
            Node::from_nodes(iter.collect())
        } else {
            debug_assert!(n_children <= 2 * MAX_CHILDREN);
            // Note: Splitting at midpoint is another option
            let splitpoint = (2 * MAX_CHILDREN + n_children) / 4;
            let left = Node::from_nodes(iter.by_ref().take(splitpoint).collect());
            let right = Node::from_nodes(iter.collect());
            Node::merge_two(left, right)
        }
    }

    /// Concatenates two nodes of possibly different heights into a single node.
    pub fn concat(node1: Node<I, L>, node2: Node<I, L>) -> Node<I, L> {
        let h1 = node1.height();
        let h2 = node2.height();

        match h1.cmp(&h2) {
            cmp::Ordering::Less => {
                let children2 = node2.get_children();
                if h1 == h2 - 1 && node1.has_min_size() {
                    Node::merge_nodes(&[node1], children2)
                } else {
                    let newnode = Node::concat(node1, children2[0].clone());
                    if newnode.height() == h2 - 1 {
                        Node::merge_nodes(&[newnode], &children2[1..])
                    } else { // newnode.height() == h2
                        Node::merge_nodes(newnode.get_children(), &children2[1..])
                    }
                }
            },
            cmp::Ordering::Equal => {
                if node1.has_min_size() && node2.has_min_size() {
                    Node::merge_two(node1, node2)
                } else {
                    Node::merge_nodes(node1.get_children(), node2.get_children())
                }
            },
            cmp::Ordering::Greater => {
                let children1 = node1.get_children();
                if h2 == h1 - 1 && node2.has_min_size() {
                    Node::merge_nodes(children1, &[node2])
                } else {
                    let lastix = children1.len() - 1;
                    let newnode = Node::concat(children1[lastix].clone(), node2);
                    if newnode.height() == h1 - 1 {
                        Node::merge_nodes(&children1[..lastix], &[newnode])
                    } else {
                        Node::merge_nodes(&children1[..lastix], newnode.get_children())
                    }
                }
            }
        }
    }
}

impl<I: Info, L: Leaf<I=I>> LeftTree<I, L> {
    pub fn new() -> LeftTree<I, L> {
        LeftTree { root: None }
    }

    pub fn push_back(&mut self, node: Node<I, L>) {
        let root = match self.root.take() {
            Some(root) => Node::concat(root, node),
            None => node,
        };
        self.root = Some(root);
    }

    pub fn push_front(&mut self, node: Node<I, L>) {
        let root = match self.root.take() {
            Some(root) => Node::concat(node, root),
            None => node,
        };
        self.root = Some(root);
    }

    //pub fn walk<T>(&self, f: F, ctx) -> Option<T> where F: FnMut(node, ctx) -> Action<T> {}
    //pub fn walk_split(&mut self, f: F, ctx) -> LeftTree<I, L> where F: FnMut(node, ctx) -> Action<Split> {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct TestLeaf(usize);

    impl Leaf for TestLeaf {
        type I = usize;
        fn compute_info(&self) -> usize {
            self.0
        }
    }

    fn root_of<I: Info, L: Leaf<I=I>>(tree: &LeftTree<I, L>) -> &Node<I, L> {
        tree.root.as_ref().unwrap()
    }

    fn info_of<I: Info, L: Leaf<I=I>>(tree: &LeftTree<I, L>) -> &I {
        root_of(&tree).info()
    }

    fn height_of<I: Info, L: Leaf<I=I>>(tree: &LeftTree<I, L>) -> usize {
        root_of(&tree).height()
    }

    #[test]
    fn basics() {
        let mut tree = LeftTree::new();
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
