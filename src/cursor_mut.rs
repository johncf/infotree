use super::*;
use node::{LeafMut, insert_maybe_split, balance_maybe_merge};

use std::fmt;
use std::iter::FromIterator;
use std::mem;

// Note: The working of `CursorMut` is fundamentally different from `Cursor`. `CursorMut` can
//       become empty (iff `cur_node` is empty. `cur_node` empty implies `steps` is also empty).

/// A cursor object that can be used to modify internals of `Node` while maintaining balance.
///
/// `CursorMut` is heavier compared to `Cursor`. Even though `CursorMut` does not do any heap
/// allocations for its own operations, most operations tries to make the current node writable
/// using `Arc::make_mut`. This could result in a heap allocation if the number of references to
/// that node is more than one.
#[derive(Clone)]
pub struct CursorMut<L: Leaf, P> {
    cur_node: Node<L>,
    steps: CVec<CursorMutStep<L, P>>,
}

#[derive(Clone)]
struct CursorMutStep<L: Leaf, P> {
    nodes: RC<NVec<Node<L>>>,
    idx: usize,
    path_info: P,
}

impl<L, P> fmt::Debug for CursorMutStep<L, P> where L: Leaf, P: PathInfo<L::Info> + fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CursorMutStep {{ nodes.len: {}, idx: {}, path_info: {:?} }}",
                  self.nodes.len(), self.idx, self.path_info)
    }
}

impl<L, P> CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    pub fn new() -> CursorMut<L, P> {
        CursorMut {
            cur_node: Node::never(),
            steps: CVec::new(),
        }
    }

    pub fn from_node(node: Node<L>) -> CursorMut<L, P> {
        CursorMut {
            cur_node: node,
            steps: CVec::new(),
        }
    }

    pub fn into_root(mut self) -> Option<Node<L>> {
        self.reset();
        self.take_current()
    }

    pub fn current(&self) -> Option<&Node<L>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref node => Some(node),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.current().is_none()
    }

    /// Returns whether the cursor is currently at the root of the tree.
    ///
    /// Returns `true` even if the cursor is empty.
    pub fn is_root(&self) -> bool {
        self.steps.len() == 0
    }

    /// Height of the current node from leaves.
    pub fn height(&self) -> Option<usize> {
        self.current().map(|node| node.height())
    }

    /// Returns a mutable reference to the leaf's value if the current node is a leaf.
    pub fn leaf_mut(&mut self) -> Option<LeafMut<L>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref mut cur_node => cur_node.leaf_mut(),
        }
    }

    /// The cumulative info along the path from root to this node. Returns `P::identity()` if the
    /// current node is root or cursor is empty.
    pub fn path_info(&self) -> P {
        match self.steps.last() {
            Some(cstep) => cstep.path_info,
            None => P::identity(),
        }
    }

    /// The `path_info` till this node and after.
    ///
    /// Returns `Some((p, p.extend(current.info())))` where `p` is `path_info()` if cursor is
    /// non-empty, `None` otherwise.
    pub fn path_interval(&self) -> Option<(P, P)> {
        match self.current() {
            Some(cur_node) => Some({
                let path_info = self.path_info();
                (path_info, path_info.extend(cur_node.info()))
            }),
            None => None,
        }
    }

    /// Returns the position of the current node with respect to its sibling nodes. The pair
    /// indicate `(left_index, right_index)`, or more simply, the number of siblings to the left
    /// and to the right respectively.
    pub fn position(&self) -> Option<(usize, usize)> {
        self.steps.last().map(|cstep| (cstep.idx, cstep.nodes.len() - cstep.idx - 1))
    }
}

// navigational methods
impl<L, P> CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    pub fn reset(&mut self) {
        while let Some(_) = self.ascend() {}
    }

    pub fn ascend(&mut self) -> Option<&Node<L>> {
        match self.steps.pop() {
            Some(CursorMutStep { nodes, idx, .. }) => {
                self.ascend_raw(nodes, idx);
                self.current()
            }
            None => { // cur_node is the root (or empty)
                None
            }
        }
    }

    pub fn descend_first_till(&mut self, height: usize) {
        while let Some(h) = self.height() {
            if h > height { self.descend_left(0); }
            else { break }
        }
    }

    pub fn descend_last_till(&mut self, height: usize) {
        while let Some(h) = self.height() {
            if h > height { self.descend_right(0); }
            else { break }
        }
    }

    pub fn descend_left(&mut self, idx: usize) -> Option<&Node<L>> {
        self.descend_by(|_, _, i, _| i == idx, false)
    }

    pub fn descend_right(&mut self, idx: usize) -> Option<&Node<L>> {
        self.descend_by(|_, _, _, i| i == idx, true)
    }

    /// Descend the tree once, on the child for which `f` returns `true`.
    ///
    /// Returns `None` if cursor is empty or is at a leaf node, or if `f` returned `false` on all
    /// children.
    ///
    /// The arguments to `f` are treated exactly the same as in [`Node::path_traverse`].
    ///
    /// Panics if tree depth is greater than 8.
    ///
    /// [`Node::path_traverse`]: ../enum.Node.html#method.path_traverse
    pub fn descend_by<F>(&mut self, f: F, reversed: bool) -> Option<&Node<L>>
        where F: FnMut(P, L::Info, usize, usize) -> bool
    {
        match self.take_current() {
            Some(cur_node) => {
                let res = if reversed {
                    cur_node.path_traverse_rev(self.path_info(), f)
                } else {
                    cur_node.path_traverse(self.path_info(), f)
                }.map(|(index, path_info, _)| (index, path_info));

                match res {
                    Ok((index, path_info)) => {
                        self.descend_raw(cur_node.into_children_must(), index, path_info);
                        debug_assert!(!self.cur_node.is_never());
                        Some(&self.cur_node)
                    }
                    Err(_) => {
                        self.cur_node = cur_node;
                        None
                    },
                }
            }
            None => None, // empty cursor
        }
    }

    /// Moves the cursor to the first leaf node which satisfy the following condition:
    ///
    /// `info_sub <= node.info()`
    ///
    /// And returns a reference to it. If no such leaf was found, returns `None` and cursor will
    /// point to the root node.
    ///
    /// For this to work correctly, the leaves of the tree must be sorted by the subfield of
    /// `node.info()` represented by `info_sub` in ascending order, and `L::Info::gather` must
    /// apply the "max" function on this field.
    pub fn find<IS: SubOrd<L::Info>>(&mut self, _info_sub: IS) -> Option<&Node<L>> {
        unimplemented!()
    }

    /// Moves the cursor to the first leaf node which satisfy the following condition:
    ///
    /// `path_info <= path_info_sub <= path_info.extend(node.info())`
    ///
    /// And returns a reference to it. If no such leaf was found, returns `None` and cursor will
    /// point to the root node.
    ///
    /// For this to work correctly, `P::identity()` value should be the smallest value (possibly
    /// the "zero" value) in the `P` domain, and `L::Info` should not allow "negative" values so
    /// that path-info is non-decreasing when `extend`-ed with `L::Info` values.
    pub fn goto<PS: SubOrd<P>>(&mut self, _path_info_sub: PS) -> Option<&Node<L>> {
        unimplemented!()
    }

    /// Make the cursor point to the next element at the same height.
    ///
    /// If there is no next element, it returns `None` and cursor resets to root.
    pub fn next_node(&mut self) -> Option<&Node<L>> {
        let mut depth_delta = 0;
        loop {
            match self.steps.pop() {
                Some(CursorMutStep { mut nodes, mut idx, mut path_info }) => {
                    debug_assert!(!self.cur_node.is_never());
                    if idx + 1 < nodes.len() {
                        { // nodes mut borrow
                            let nodes = RC::make_mut(&mut nodes);
                            path_info = path_info.extend(self.cur_node.info());
                            self.swap_current(nodes, idx);
                            idx += 1;
                            self.swap_current(nodes, idx);
                        }
                        self.steps.push(CursorMutStep { nodes, idx, path_info });
                        while depth_delta > 0 {
                            self.descend_left(0).unwrap();
                            depth_delta -= 1;
                        }
                        return Some(&self.cur_node);
                    } else {
                        self.ascend_raw(nodes, idx);
                        depth_delta += 1;
                    }
                }
                None => return None, // at the root
            }
        }
    }

    /// Make the cursor point to the previous element at the same height.
    ///
    /// If there is no previous element, it returns `None` and cursor resets to root.
    pub fn prev_node(&mut self) -> Option<&Node<L>> {
        let mut depth_delta = 0;
        loop {
            match self.steps.pop() {
                Some(CursorMutStep { mut nodes, mut idx, mut path_info }) => {
                    debug_assert!(!self.cur_node.is_never());
                    if idx > 0 {
                        { // nodes mut borrow
                            let nodes = RC::make_mut(&mut nodes);
                            self.swap_current(nodes, idx);
                            idx -= 1;
                            self.swap_current(nodes, idx);
                            path_info = path_info.extend_inv(self.cur_node.info());
                        }
                        self.steps.push(CursorMutStep { nodes, idx, path_info });
                        while depth_delta > 0 {
                            self.descend_right(0).unwrap();
                            depth_delta -= 1;
                        }
                        return Some(&self.cur_node);
                    } else {
                        self.ascend_raw(nodes, idx);
                        depth_delta += 1;
                    }
                }
                None => return None, // at the root
            }
        }
    }
}

// structural modifications
impl<L, P> CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    /// Insert `leaf` at the current position if at the bottom of tree, or insert it as the first
    /// leaf under the current node.
    ///
    /// It is unspecified where the cursor will be after this operation. But it is guaranteed that
    /// `path_info` will not decrease (or `extend_inv`). The user should ensure that the cursor is
    /// at the intended location after this.
    pub fn insert_first(&mut self, leaf: L) {
        self.descend_first_till(0);
        self.insert_raw(Node::from_leaf(leaf), false);
    }

    /// Same as `insert_first` but insert after the current node if at the bottom of tree, or
    /// insert it as the last leaf under the current node.
    ///
    /// The cursor behavior is the same as `insert_first`.
    pub fn insert_last(&mut self, leaf: L) {
        self.descend_last_till(0);
        self.insert_raw(Node::from_leaf(leaf), true);
    }

    /// Remove the first leaf under the current node.
    pub fn remove_first(&mut self) -> Option<L> {
        self.descend_first_till(0);
        self.remove_node().and_then(|n| n.into_leaf().ok())
    }

    /// Remove the current node and return it. If the cursor is empty, return `None`.
    ///
    /// It is unspecified where the cursor will be after this operation. But it is guaranteed that
    /// `path_info` will not increase (or `extend`). The user should ensure that the cursor is at
    /// the correct location after this.
    pub fn remove_node(&mut self) -> Option<Node<L>> {
        match self.take_current() {
            Some(cur_node) => {
                match self.steps.pop() {
                    Some(mut cstep) => {
                        let dummy = RC::make_mut(&mut cstep.nodes).remove(cstep.idx).unwrap();
                        debug_assert!(dummy.is_never());
                        if cstep.nodes.len() > 0 {
                            self.fix_current(cstep);
                        } else {
                            debug_assert!(self.steps.len() == 0); // should be root
                        }
                    }
                    None => (),
                }
                Some(cur_node)
            },
            None => None, // cursor is empty
        }
    }

    /// Merge the current node with `node` on its right and balance. `node` can be of any height.
    pub fn merge_right(&mut self, _node: Node<L>) {
        unimplemented!()
    }

    /// Merge the current node with `node` on its left and balance. `node` can be of any height.
    pub fn merge_left(&mut self, _node: Node<L>) -> Option<L> {
        unimplemented!()
    }

    /// Split the tree into two, and return the right part of it. The current node, all leaves
    /// under it, as well as all leaves to the right of it will be included in the returned tree.
    ///
    /// **Not yet implemented.**
    pub fn split_off(&mut self) -> Node<L> {
        // This can be done with repeated `Node::concat` on both "sides" (`self` and output) with a
        // complexity of `log n`. This can possibly also be done with the same complexity with
        // `merge_adjacent` called at height where the split was started on both "sides" (which
        // might stop before reaching root, in which case ascend and call again), but some of the
        // conditions asserted by that function would need to be relaxed.
        unimplemented!()
    }
}

impl<L, P> CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    fn insert_raw(&mut self, newnode: Node<L>, after: bool) {
        match self.current() {
            Some(_) => {
                assert_eq!(self.cur_node.height(), newnode.height());
                match self.steps.pop() {
                    Some(CursorMutStep { mut nodes, mut idx, mut path_info }) => {
                        let maybe_split = {
                            let nodes = RC::make_mut(&mut nodes);
                            let cur_info = self.cur_node.info();
                            self.swap_current(nodes, idx);
                            if after {
                                path_info = path_info.extend(cur_info);
                                idx += 1;
                            }
                            insert_maybe_split(nodes, idx, newnode)
                        };
                        // now self.cur_node.is_never() // checked in swap_current
                        if let Some(split_node) = maybe_split {
                            let parent = Node::from_children(nodes); // gather info
                            self.cur_node = parent;
                            self.insert_raw(split_node, true);
                        } else {
                            self.swap_current(RC::make_mut(&mut nodes), idx);
                            self.steps.push(CursorMutStep { nodes, idx, path_info });
                        }
                    }
                    None => { // cur_node is the root
                        self.cur_node = if after {
                            Node::concat(self.take_current().unwrap(), newnode)
                        } else {
                            Node::concat(newnode, self.take_current().unwrap())
                        };
                    }
                }
            }
            None => { // cursor was empty
                self.cur_node = newnode;
            }
        }
    }

    // Find a replacement node for the current node. May ascend the tree multiple times.
    fn fix_current(&mut self, cstep: CursorMutStep<L, P>) {
        debug_assert!(self.cur_node.is_never());
        let CursorMutStep { mut nodes, mut idx, mut path_info } = cstep;
        let nodes_len = nodes.len();
        debug_assert!(nodes_len > 0); // nodes should never be empty
        let steps_len = self.steps.len();
        if nodes_len >= MIN_CHILDREN || steps_len == 0 {
            if idx == nodes_len {
                idx -= 1;
            }
            self.swap_current(RC::make_mut(&mut nodes), idx);
            debug_assert!(self.cur_node.children().map_or(true, |c| c.len() >= MIN_CHILDREN));
            path_info = path_info.extend_inv(self.cur_node.info());
            self.steps.push(CursorMutStep { nodes, idx, path_info });
        } else { // steps_len > 0
            debug_assert_eq!(nodes_len, MIN_CHILDREN - 1);
            self.cur_node = Node::from_children(nodes);
            self.merge_adjacent();
        }
    }

    // Merge the current node with an adjacent sibling to make it balanced.
    fn merge_adjacent(&mut self) {
        debug_assert!(!self.cur_node.is_never());
        debug_assert_eq!(self.cur_node.children().unwrap().len(), MIN_CHILDREN - 1);
        let CursorMutStep { mut nodes, mut idx, mut path_info } = self.steps.pop().unwrap();
        if nodes.len() == 1 { // cur_node is the only child
            debug_assert!(self.steps.len() == 0); // the parent must be root
            return; // cur_node becomes the root
        }
        let at_right_end = idx + 1 == nodes.len(); // merge with the right node by default
        debug_assert!(nodes.len() > 1);
        let merged;
        {
            let nodes = RC::make_mut(&mut nodes);
            merged = if at_right_end {
                let left_node = nodes.get_mut(idx - 1).unwrap();
                path_info = path_info.extend_inv(left_node.info());
                balance_maybe_merge(left_node.children_mut_must(), self.cur_node.children_mut_must())
            } else {
                let right_node = nodes.get_mut(idx + 1).unwrap();
                balance_maybe_merge(self.cur_node.children_mut_must(), right_node.children_mut_must())
            };
            if merged {
                if !at_right_end {
                    nodes.remove(idx + 1).unwrap(); // remove the now empty right_node
                    self.swap_current(nodes, idx);
                }
                debug_assert!(self.cur_node.is_never());
            } else {
                if at_right_end {
                    self.swap_current(nodes, idx);
                    idx -= 1; // make left_node be the current node (for path_info correctness)
                    self.swap_current(nodes, idx);
                }
                debug_assert!(!self.cur_node.is_never());
            }
        };
        let cstep = CursorMutStep { nodes, idx, path_info };
        if merged {
            self.fix_current(cstep);
        } else {
            let _res = self.steps.push(cstep);
            debug_assert!(_res.is_none());
        }
    }

    fn ascend_raw(&mut self, mut nodes: RC<NVec<Node<L>>>, idx: usize) {
        debug_assert!(!self.cur_node.is_never());
        self.swap_current(RC::make_mut(&mut nodes), idx);
        let parent = Node::from_children(nodes); // gather info
        self.cur_node = parent;
    }

    fn descend_raw(&mut self, mut nodes: RC<NVec<Node<L>>>, idx: usize, path_info: P) {
        debug_assert!(self.cur_node.is_never());
        self.swap_current(RC::make_mut(&mut nodes), idx);
        let _res = self.steps.push(CursorMutStep { nodes, idx, path_info });
        assert!(_res.is_none(), "Exceeded maximum supported depth.");
    }

    fn swap_current(&mut self, nodes: &mut NVec<Node<L>>, idx: usize) {
        let _never_before = self.cur_node.is_never();
        mem::swap(&mut self.cur_node, nodes.get_mut(idx).unwrap());
        debug_assert!(self.cur_node.is_never() != _never_before);
    }

    fn take_current(&mut self) -> Option<Node<L>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref mut cur_node => Some(mem::replace(cur_node, Node::never())),
        }
    }
}

impl<L, P> FromIterator<L> for CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    fn from_iter<J: IntoIterator<Item=L>>(iter: J) -> Self {
        let mut curs = CursorMut::new();
        let mut iter = iter.into_iter().map(|e| Node::from_leaf(e));

        loop {
            curs.descend_last_till(1);
            let nodes: NVec<_> = iter.by_ref().take(MAX_CHILDREN).collect();
            if nodes.len() > 0 {
                curs.insert_raw((Node::from_children(RC::new(nodes))), true);
            } else {
                break;
            }
        }
        curs
    }
}

#[cfg(test)]
mod tests {
    use super::CursorMut;
    use ::test_help::*;

    type CursorMutT<L> = CursorMut<L, ()>;

    #[test]
    fn insert() {
        let mut cursor_mut = CursorMutT::new();
        for i in 0..128 {
            cursor_mut.insert_last(TestLeaf(i));
        }
        let root = cursor_mut.into_root().unwrap();
        let mut cursor = CursorT::new(&root);
        for i in 0..128 {
            assert_eq!(cursor.next_leaf(), Some(&TestLeaf(i)));
        }
        assert_eq!(cursor.next_leaf(), None);
    }

    #[test]
    fn delete() {
        let mut cursor_mut = CursorMutT::new();
        for i in 0..128 {
            cursor_mut.insert_last(TestLeaf(i));
        }
        cursor_mut.reset();
        for i in 0..128 {
            cursor_mut.descend_first_till(0);
            assert_eq!(cursor_mut.remove_first(), Some(TestLeaf(i)));
        }
        assert_eq!(cursor_mut.is_empty(), true);
    }

    #[test]
    fn from_iter() {
        let cursor_mut: CursorMutT<_> = (0..128).map(|i| TestLeaf(i)).collect();
        let root = cursor_mut.into_root().unwrap();
        let mut cursor = CursorT::new(&root);
        for i in 0..128 {
            assert_eq!(cursor.next_leaf(), Some(&TestLeaf(i)));
        }
        assert_eq!(cursor.next_leaf(), None);
    }

    #[test]
    fn root_balance() {
        let mut cursor_mut: CursorMutT<_> = (0..2).map(|i| TestLeaf(i)).collect();
        cursor_mut.remove_first();
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(1)); // allow root with single leaf child

        let mut cursor_mut: CursorMutT<_> = (0..17).map(|i| TestLeaf(i)).collect();
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(2));
        cursor_mut.descend_left(0);
        cursor_mut.remove_node(); // now root has only one child
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(2));
        cursor_mut.remove_first();
        cursor_mut.remove_first();
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(1));
    }

    #[test]
    fn node_iter() {
        let mut cursor_mut: CursorMutT<_> = (0..128).map(|i| TestLeaf(i)).collect();
        cursor_mut.reset();
        cursor_mut.descend_first_till(0);
        assert_eq!(cursor_mut.current().and_then(|n| n.leaf()), Some(&TestLeaf(0)));
        for i in 1..128 {
            assert_eq!(cursor_mut.next_node().and_then(|n| n.leaf()), Some(&TestLeaf(i)));
        }
        assert_eq!(cursor_mut.next_node().and_then(|n| n.leaf()), None);
    }

    // FIXME need more tests
}
