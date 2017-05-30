use super::*;

use std::fmt;
use std::iter::FromIterator;
use std::mem;

// Note: The working of `CursorMut` is fundamentally different from `Cursor`. `CursorMut` can
//       become empty (iff `cur_node` is empty. `cur_node` empty implies `steps` is also empty).

/// A useful type alias for easy initialization of `CursorMut`.
pub type CursorMutT<L> = CursorMut<L, ()>;

/// A cursor object that can be used to modify internals of `Node` while maintaining balance.
///
/// `CursorMut` is heavier compared to `Cursor`. Even though `CursorMut` does not do any heap
/// allocations for its own operations, most operations tries to make the current node writable
/// using `Arc::make_mut`. This could result in a heap allocation if the number of references to
/// that node is more than one.
pub struct CursorMut<L: Leaf, P> {
    cur_node: Node<L>,
    steps: CVec<CursorMutStep<L, P>>,
}

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

    pub fn is_empty(&self) -> bool {
        self.current().is_none()
    }

    pub fn current(&self) -> Option<&Node<L>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref node => Some(node),
        }
    }

    /// Returns a mutable reference to the leaf's value if the current node is a leaf.
    pub fn leaf_mut(&mut self) -> Option<LeafMut<L>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref mut cur_node => cur_node.leaf_mut(),
        }
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

    /// The cumulative info along the path from root to this node. Returns `P::identity()` if the
    /// current node is root.
    pub fn path_info(&self) -> P {
        match self.steps.last() {
            Some(cstep) => cstep.path_info,
            None => P::identity(),
        }
    }

    pub fn reset(&mut self) {
        while let Some(_) = self.ascend() {}
    }

    pub fn ascend(&mut self) -> Option<&Node<L>> {
        match self.steps.pop() {
            Some(CursorMutStep { mut nodes, idx, .. }) => {
                mem::swap(&mut self.cur_node, RC::make_mut(&mut nodes).get_mut(idx).unwrap());
                debug_assert!(self.cur_node.is_never());
                let parent = Node::from_children(nodes); // gather info
                self.cur_node = parent;
                self.current()
            }
            None => { // cur_node is the root
                None
            }
        }
    }

    pub fn descend_first(&mut self, idx: usize) -> Option<&Node<L>> {
        self.descend_extended(|_, _, i, _| i == idx, false)
    }

    pub fn descend_last(&mut self, idx: usize) -> Option<&Node<L>> {
        self.descend_extended(|_, _, _, i| i == idx, true)
    }

    pub fn descend_first_till(&mut self, height: usize) {
        while let Some(h) = self.height() {
            if h > height { self.descend_first(0); }
            else { break }
        }
    }

    pub fn descend_last_till(&mut self, height: usize) {
        while let Some(h) = self.height() {
            if h > height { self.descend_last(0); }
            else { break }
        }
    }

    /// Descend the tree once, on the child for which `f` returns `true`. It internally calls
    /// `descend_extended` for path info book-keeping.
    ///
    /// Returns `None` if `f` returned `false` on all children, or if it was a leaf node.
    ///
    /// The arguments to `f` are exactly the same as in [`Node::traverse`].
    ///
    /// [`Node::traverse`]: ../enum.Node.html#method.traverse
    pub fn descend<F>(&mut self, mut f: F, reversed: bool) -> Option<&Node<L>>
        where F: FnMut(L::Info, usize, usize) -> bool
    {
        self.descend_extended(|_, a, i, j| f(a, i, j), reversed)
    }

    /// Similar to descend, with the arguments to `f` treated exactly the same as in
    /// [`Node::path_traverse`].
    ///
    /// Panics if tree depth is greater than 8.
    pub fn descend_extended<F>(&mut self, f: F, reversed: bool) -> Option<&Node<L>>
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

    /// Insert a leaf at the current position if currently focused on a leaf, or as the first leaf
    /// under the current node.
    ///
    /// It is unspecified where the cursor will be after this operation. But it is guaranteed that
    /// `path_info` will not decrease (or `extend_inv`). The user should ensure that the cursor is
    /// at the intended location after this.
    pub fn insert(&mut self, leaf: L) {
        self.descend_first_till(0);
        self.insert_raw(Node::from_leaf(leaf), false);
    }

    /// Same as `insert` but insert after the current node (incl. all its leaf children).
    pub fn insert_after(&mut self, leaf: L) {
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
                match self.steps.last_mut() {
                    Some(cstep) => {
                        let cur_dummy = RC::make_mut(&mut cstep.nodes).remove(cstep.idx).unwrap();
                        debug_assert!(cur_dummy.is_never());
                    }
                    None => (),
                }
                self.fix_current();
                Some(cur_node)
            },
            None => None, // cursor is empty
        }
    }

    /// Split the tree into two, and return the right part of it. The current node, all leaves
    /// under it, as well as all leaves to the right of it will be included in the returned tree.
    pub fn split_off(&mut self) -> Node<L> {
        unimplemented!()
    }
}

impl<L, P> CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    fn insert_raw(&mut self, newnode: Node<L>, after: bool) {
        match self.take_current() {
            Some(mut cur_node) => {
                assert_eq!(cur_node.height(), newnode.height());
                match self.steps.pop() {
                    Some(CursorMutStep { mut nodes, mut idx, mut path_info }) => {
                        let maybe_split = {
                            let nodes = RC::make_mut(&mut nodes);
                            let cur_info = cur_node.info();
                            mem::swap(&mut cur_node, nodes.get_mut(idx).unwrap());
                            if after {
                                path_info = path_info.extend(cur_info);
                                idx += 1;
                            }
                            insert_maybe_split(nodes, idx, newnode)
                        };
                        debug_assert!(cur_node.is_never());
                        if let Some(split_node) = maybe_split {
                            let parent = Node::from_children(nodes); // gather info
                            self.cur_node = parent;
                            self.insert_raw(split_node, true);
                        } else {
                            mem::swap(&mut self.cur_node, RC::make_mut(&mut nodes).get_mut(idx).unwrap());
                            self.steps.push(CursorMutStep { nodes, idx, path_info });
                        }
                        debug_assert!(!self.cur_node.is_never());
                    }
                    None => { // cur_node is the root
                        self.cur_node = if after {
                            Node::concat(cur_node, newnode)
                        } else {
                            Node::concat(newnode, cur_node)
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
    fn fix_current(&mut self) {
        debug_assert!(self.cur_node.is_never());
        if let Some(CursorMutStep { mut nodes, mut idx, mut path_info }) = self.steps.pop() {
            let nodes_len = nodes.len();
            let steps_len = self.steps.len();
            if nodes_len >= MIN_CHILDREN || (steps_len == 0 && nodes_len > 0) {
                if idx == nodes_len {
                    idx -= 1;
                }
                mem::swap(&mut self.cur_node, RC::make_mut(&mut nodes).get_mut(idx).unwrap());
                if nodes_len > 1 { // nodes is non-empty after remove
                    path_info = path_info.extend_inv(self.current().unwrap().info());
                    self.steps.push(CursorMutStep { nodes, idx, path_info });
                }
            } else if steps_len > 0 {
                debug_assert_eq!(nodes_len, MIN_CHILDREN - 1);
                self.cur_node = Node::from_children(nodes);
                self.merge_adjacent();
            } else {
                debug_assert!(false); // unreachable! nodes should never be empty
            }
        } // else { the cursor became empty. nothing to do. }
    }

    // Merge the current node with an adjacent one to make it balanced.
    fn merge_adjacent(&mut self) {
        debug_assert!(!self.cur_node.is_never());
        let CursorMutStep { mut nodes, mut idx, mut path_info } = self.steps.pop().unwrap();
        let at_right_end = idx + 1 == nodes.len(); // merge with the right node by default
        debug_assert!(nodes.len() > 0);
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
                    mem::swap(&mut self.cur_node, nodes.get_mut(idx).unwrap());
                }
                debug_assert!(self.cur_node.is_never());
            } else {
                if at_right_end {
                    mem::swap(&mut self.cur_node, nodes.get_mut(idx).unwrap());
                    idx -= 1; // make left_node be the current node (for path_info correctness)
                    mem::swap(&mut self.cur_node, nodes.get_mut(idx).unwrap());
                }
                debug_assert!(!self.cur_node.is_never());
            }
        };
        let _res = self.steps.push(CursorMutStep { nodes, idx, path_info });
        debug_assert!(_res.is_none());
        if merged { self.fix_current(); }
    }

    fn descend_raw(&mut self, mut nodes: RC<NVec<Node<L>>>, idx: usize, path_info: P) {
        debug_assert!(self.current().is_none());
        mem::swap(&mut self.cur_node, RC::make_mut(&mut nodes).get_mut(idx).unwrap());
        let _res = self.steps.push(CursorMutStep { nodes, idx, path_info });
        assert!(_res.is_none()); // panic if depth was 8
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
    use super::*;
    use ::tests::*;

    #[test]
    fn insert() {
        let mut cursor_mut = CursorMutT::new();
        for i in 0..128 {
            cursor_mut.insert_after(TestLeaf(i));
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
            cursor_mut.insert_after(TestLeaf(i));
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

    // FIXME need more tests
}
