//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! Both design and implementation are heavily based on [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope
extern crate arrayvec;
extern crate mines;

use std::cmp;
use std::ops::{Deref, DerefMut};

use arrayvec::ArrayVec;
use mines::boom;

pub mod cursor;
pub mod cursor_mut;

pub mod info_ext;
mod info_tree;

pub use info_ext::PathInfo;
pub use cursor::CursorT;
pub use cursor_mut::CursorMutT;
pub use info_tree::InfoTree;

const MIN_CHILDREN: usize = 8;
const MAX_CHILDREN: usize = 16;

//trait Mutable: Deref {
//    fn make_mut(this: &mut Self) -> &mut Self::Target;
//}
//
//impl<T> Mutable for Box<T> {
//    fn make_mut(this: &mut Box<T>) -> &mut T {
//        &mut *this
//    }
//}
//
// Uncomment the above block, and RC can be assigned the type Box<T>
// This gives around 20-40% speedup!
// Note that `Arc::clone` or `Rc::clone` methods are never used directly (`clone` may be indirectly
// called by `make_mut` if ref-count > 1).

type RC<T> = std::sync::Arc<T>; // replace with std::rc::Rc<T> to get significant speed-up.
type NVec<T> = ArrayVec<[T; MAX_CHILDREN]>;

// Maximum height of tree that can be handled by cursor types.
const CURSOR_MAX_HT: usize = 8;
// => Maximum number of elements = MAX_CHILDREN^CURSOR_P2R_SIZE = 16^8 = 2^32

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;

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
    Never(NeverVal), // for use with CursorMut
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

#[derive(Clone)]
pub struct NeverVal(Private);

#[derive(Clone)]
struct Private;

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
    pub fn from_children(nodes: RC<NVec<Node<L>>>) -> Node<L> {
        let height = nodes[0].height() + 1;
        let mut info = nodes[0].info();
        for child in &nodes[1..] {
            assert_eq!(height, child.height() + 1);
            info = info.gather(child.info());
        }
        Node::Internal(InternalVal { info, height, nodes })
    }

    /// Tries to unwrap the node into leaf. If node is internal, `Err(self)` is returned.
    pub fn into_leaf(self) -> Result<L, Node<L>> {
        match self {
            Node::Internal(_) => Err(self),
            Node::Leaf(LeafVal { val, .. }) => Ok(val),
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    /// Tries to unwrap the node into its children. If node is leaf, `Err(self)` is returned.
    pub fn into_children(self) -> Result<RC<NVec<Node<L>>>, Node<L>> {
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
    pub fn children(&self) -> Option<&NVec<Node<L>>> {
        match *self {
            Node::Internal(ref int) => Some(&*int.nodes),
            Node::Leaf(_) => None,
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

    /// Get a mutable reference to the leaf value if this is a leaf node, otherwise return `None`.
    pub fn leaf_mut(&mut self) -> Option<LeafMut<L>> {
        match self {
            &mut Node::Internal(_) => None,
            &mut Node::Leaf(ref mut leaf) => Some(LeafMut(leaf)),
            &mut Node::Never(_) => unsafe { boom("Never!") },
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
            &Node::Never(_) => unsafe { boom("Never!") },
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
            &Node::Never(_) => unsafe { boom("Never!") },
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
                let mut children2 = node2.into_children_must();
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
                            let mut newchildren = newnode.into_children_must();
                            if {
                                let newchildren = RC::make_mut(&mut newchildren);
                                std::mem::swap(newchildren, children2);
                                balance_maybe_merge(children2, newchildren)
                            } { // merged into children2
                                None
                            } else {
                                Some(Node::from_children(newchildren))
                            }
                        }
                    }
                };
                (Node::from_children(children2), maybe_newnode)
            },
            cmp::Ordering::Equal => {
                if node1.has_min_size() && node2.has_min_size() {
                    (node1, Some(node2))
                } else {
                    let mut children1 = node1.into_children_must();
                    let mut children2 = node2.into_children_must();
                    if balance_maybe_merge(RC::make_mut(&mut children1), RC::make_mut(&mut children2)) {
                        (Node::from_children(children1), None)
                    } else {
                        (Node::from_children(children1), Some(Node::from_children(children2)))
                    }
                }
            },
            cmp::Ordering::Greater => {
                let mut children1 = node1.into_children_must();
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
                            let mut newchildren = newnode.into_children_must();
                            if {
                                let newchildren = RC::make_mut(&mut newchildren);
                                balance_maybe_merge(children1, newchildren)
                            } {
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
        let _res = nodes.insert(idx, newnode);
        debug_assert!(_res.is_none());
        None
    } else {
        let extra = nodes.insert(idx, newnode).unwrap(); // like unwrap_err
        let n_left = balanced_split(MAX_CHILDREN + 1).0;
        let mut after: NVec<_> = nodes.drain(n_left + 1..).collect();
        let _res = after.push(extra);
        debug_assert!(_res.is_none());
        Some(Node::from_children(RC::new(after)))
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
    fn children_must(&self) -> &NVec<Node<L>> {
        match self.children() {
            Some(nodes) => nodes,
            None => unreachable!("buggy children_must call"),
        }
    }

    fn children_mut_must(&mut self) -> &mut NVec<Node<L>> {
        match *self {
            Node::Internal(ref mut int) => RC::make_mut(&mut int.nodes),
            Node::Leaf(_) => unreachable!("buggy children_mut_must call"),
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    fn into_children_must(self) -> RC<NVec<Node<L>>> {
        match self.into_children() {
            Ok(nodes) => nodes,
            Err(_) => unreachable!("buggy into_children_must call"),
        }
    }

    fn has_min_size(&self) -> bool {
        match *self {
            Node::Internal(ref int) => int.nodes.len() >= MIN_CHILDREN,
            Node::Leaf(_) => true,
            Node::Never(_) => unsafe { boom("Never!") },
        }
    }

    fn merge_two(node1: Node<L>, node2: Node<L>) -> Node<L> {
        let mut nodes = NVec::new();
        nodes.push(node1);
        nodes.push(node2);
        Node::from_children(RC::new(nodes))
    }

    fn never() -> Node<L> {
        Node::Never(NeverVal(Private))
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

    // TODO more tests
}
