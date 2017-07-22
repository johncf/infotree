use super::conf::{CMutConf, Rc33M};
use super::nav::CursorNav;
use traits::{Leaf, PathInfo, SubOrd};
use node::{Node, NodesPtr, insert_maybe_split, balance_maybe_merge};

use std::fmt;
use std::iter::FromIterator;
use std::marker::PhantomData;

use arrayvec::ArrayVec;

// Note: The working of `CursorMut` is fundamentally different from `Cursor`. `CursorMut` can
//       become empty (iff `cur_node` is empty. `cur_node` empty implies `steps` is also empty).

/// A object that can be used to modify internals of `Node` while maintaining balance.
///
/// `CursorMut` is heavier compared to `Cursor`. Even though `CursorMut` does not make any heap
/// allocations for its own operations, most operations tries to make the current node writable
/// using `Arc::make_mut`. This could result in a heap allocation if the number of references to
/// that node is more than one.
///
/// Note: `CursorMut` takes more than 200B on stack (exact size mainly depends on the size of `PI`)
pub struct CursorMut<L, PI, CONF = Rc33M>
    where L: Leaf,
          CONF: CMutConf<L, PI>,
{
    cur_node: Node<L, CONF::Ptr>,
    steps: ArrayVec<CONF::MutStepsBuf>,
}

pub struct CMutStep<L, PI, CONF>
    where L: Leaf,
          CONF: CMutConf<L, PI>,
{
    nodes: CONF::Ptr,
    idx: usize,
    path_info: PI,
    __phantom: PhantomData<L>,
}

impl<L, PI, CONF> Clone for CursorMut<L, PI, CONF>
    where L: Leaf + Clone,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    fn clone(&self) -> Self {
        CursorMut {
            cur_node: self.cur_node.clone(),
            steps: self.steps.clone(),
        }
    }
}

impl<L, PI, CONF> Clone for CMutStep<L, PI, CONF>
    where L: Leaf + Clone,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    fn clone(&self) -> Self {
        CMutStep {
            nodes: self.nodes.clone(),
            idx: self.idx,
            path_info: self.path_info.clone(),
            __phantom: PhantomData,
        }
    }
}

impl<L, PI, CONF> CMutStep<L, PI, CONF>
    where L: Leaf,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    fn new(nodes: CONF::Ptr, idx: usize, path_info: PI) -> Self {
        let __phantom = PhantomData;
        CMutStep { nodes, idx, path_info, __phantom }
    }
}

impl<L, PI, CONF> fmt::Debug for CMutStep<L, PI, CONF>
    where L: Leaf,
          PI: fmt::Debug,
          CONF: CMutConf<L, PI>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CMutStep {{ nodes.len: {}, idx: {}, path_info: {:?} }}",
                  self.nodes.len(), self.idx, self.path_info)
    }
}

impl<L, PI, CONF> CursorMut<L, PI, CONF>
    where L: Leaf,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    pub fn new() -> Self {
        CursorMut {
            cur_node: Node::never(),
            steps: ArrayVec::new(),
        }
    }

    pub fn from_node(node: Node<L, CONF::Ptr>) -> Self {
        CursorMut {
            cur_node: node,
            steps: ArrayVec::new(),
        }
    }

    pub fn into_root(mut self) -> Option<Node<L, CONF::Ptr>> {
        self.reset();
        self.take_current()
    }

    pub fn current(&self) -> Option<&Node<L, CONF::Ptr>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref node => Some(node),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.current().is_none()
    }

    /// Height of the current node from leaves.
    pub fn height(&self) -> Option<usize> {
        self.current().map(|node| node.height())
    }

    /// Returns a reference to the leaf's value if the current node is a leaf.
    pub fn leaf(&self) -> Option<&L> {
        match self.cur_node {
            Node::Never(_) => None,
            ref cur_node => cur_node.leaf(),
        }
    }

    /// Returns whether the cursor is currently at the root of the tree.
    ///
    /// Returns `true` even if the cursor is empty.
    pub fn is_root(&self) -> bool {
        self.steps.len() == 0
    }

    /// The cumulative info along the path from root to this node. Returns `PathInfo::identity()`
    /// if the current node is root or cursor is empty.
    pub fn path_info(&self) -> PI {
        match self.steps.last() {
            Some(cstep) => cstep.path_info,
            None => PI::identity(),
        }
    }

    /// Update the leaf value in-place using `f`. This is a no-op if the current node is not a
    /// leaf.
    pub fn leaf_update<F>(&mut self, f: F) where F: FnOnce(&mut L) {
        self.cur_node.leaf_update(f);
    }

    /// The `path_info` till this node and after.
    ///
    /// Returns `Some((p, p.extend(current.info())))` where `p` is `path_info()` if cursor is
    /// non-empty, `None` otherwise.
    pub fn path_interval(&self) -> Option<(PI, PI)> {
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
    pub fn descend_by<F>(&mut self, f: F, reversed: bool) -> Option<&Node<L, CONF::Ptr>>
        where F: FnMut(PI, L::Info, usize, usize) -> bool
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

    pub fn reset(&mut self) {
        while self.ascend().is_some() {}
    }

    pub fn ascend(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        match self.pop_step() {
            Some(CMutStep { nodes, idx, .. }) => {
                self.ascend_raw(nodes, idx);
                Some(&self.cur_node)
            }
            None => { // cur_node is the root (or empty)
                None
            }
        }
    }

    pub fn descend_first(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.descend_by(|_, _, _, _| true, false)
    }

    pub fn descend_last(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.descend_by(|_, _, _, _| true, true)
    }

    pub fn left_sibling(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        let &mut CursorMut { ref mut cur_node, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CMutStep { ref mut nodes, ref mut idx, ref mut path_info, .. }) => {
                debug_assert!(!cur_node.is_never());
                if *idx > 0 {
                    let nodes = <CONF::Ptr as NodesPtr<L>>::make_mut(nodes);
                    cur_node.never_swap(&mut nodes[*idx]);
                    *idx -= 1;
                    cur_node.never_swap(&mut nodes[*idx]);

                    *path_info = path_info.extend_inv(cur_node.info());
                    Some(&*cur_node)
                } else {
                    None
                }
            }
            None => None, // at the root
        }
    }

    pub fn right_sibling(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        let &mut CursorMut { ref mut cur_node, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CMutStep { ref mut nodes, ref mut idx, ref mut path_info, .. }) => {
                debug_assert!(!cur_node.is_never());
                if *idx + 1 < nodes.len() {
                    *path_info = path_info.extend(cur_node.info());

                    let nodes = <CONF::Ptr as NodesPtr<L>>::make_mut(nodes);
                    cur_node.never_swap(&mut nodes[*idx]);
                    *idx += 1;
                    cur_node.never_swap(&mut nodes[*idx]);

                    Some(&*cur_node)
                } else {
                    None
                }
            }
            None => None, // at the root
        }
    }

    pub fn first_leaf(&mut self) -> Option<&L> {
        <Self as CursorNav>::first_leaf(self)
    }

    pub fn last_leaf(&mut self) -> Option<&L> {
        <Self as CursorNav>::last_leaf(self)
    }

    /// Make the cursor point to the next element at the same height.
    ///
    /// If there is no next element, it returns `None` and cursor resets to root.
    pub fn next_node(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        <Self as CursorNav>::next_node(self)
    }

    /// Make the cursor point to the previous element at the same height.
    ///
    /// If there is no previous element, it returns `None` and cursor resets to root.
    pub fn prev_node(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        <Self as CursorNav>::prev_node(self)
    }

    /// Calls `next_node` and returns the leaf value if it is a leaf node.
    pub fn next_leaf(&mut self) -> Option<&L> {
        <Self as CursorNav>::next_leaf(self)
    }

    /// Calls `prev_node` and returns the leaf value if it is a leaf node.
    pub fn prev_leaf(&mut self) -> Option<&L> {
        <Self as CursorNav>::prev_leaf(self)
    }

    /// Tries to return the left sibling if exists, or ascends the tree until an ancestor with a
    /// left sibling is found and returns that sibling.
    pub fn left_maybe_ascend(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        <Self as CursorNav>::left_maybe_ascend(self)
    }

    /// Tries to return the right sibling if exists, or ascends the tree until an ancestor with a
    /// right sibling is found and returns that sibling.
    pub fn right_maybe_ascend(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        <Self as CursorNav>::right_maybe_ascend(self)
    }

    /// Moves the cursor to the first leaf node which satisfy the following condition:
    ///
    /// `info_sub <= node.info()`
    ///
    /// And returns a reference to it. Returns `None` if no leaf satisfied the condition.
    ///
    /// Conditions for correctness:
    /// - The leaves of the tree must be sorted by the value represented by `info_sub` inside
    ///   `node.info()` in ascending order.
    /// - `Leaf::Info::gather` must apply the "min" function on this field.
    ///
    /// See `find_max` for examples.
    ///
    /// A more descriptive name of this might be `find_sorted_suffix_min`.
    pub fn find_min<IS>(&mut self, info_sub: IS) -> Option<&L>
        where IS: SubOrd<L::Info>,
    {
        <Self as CursorNav>::find_min(self, info_sub)
    }

    /// Moves the cursor to the last leaf node which satisfy the following condition:
    ///
    /// `info_sub >= node.info()`
    ///
    /// And returns a reference to it. Returns `None` if no leaf satisfied the condition.
    ///
    /// Conditions for correctness is the same as `find_min`, except that `Leaf::Info::gather` must
    /// apply the "max" function on this field, instead of "min".
    ///
    /// Note: If exactly one leaf satisfies equality with `info_sub`, then both `find_max` and
    /// `find_min` will return the same element. Here are some examples:
    ///
    /// ```text
    /// leaf:     ('c', 2)   ('j', 1)   ('j', 4)   ('v', 2)
    /// find_min('j') == Some(('j', 1))
    /// find_max('j') == find_max('k') == Some(('j', 4))
    /// find_min('k') == find_max('z') == Some(('v', 2))
    /// find_min('z') == find_max('a') == None
    /// ```
    ///
    /// A more descriptive name of this might be `find_sorted_prefix_max`.
    pub fn find_max<IS>(&mut self, info_sub: IS) -> Option<&L>
        where IS: SubOrd<L::Info>,
    {
        <Self as CursorNav>::find_max(self, info_sub)
    }

    /// Moves the cursor to the first leaf node which satisfy the following condition:
    ///
    /// `path_info_sub <= path_info`
    ///
    /// And returns a reference to it. Returns `None` if no leaf satisfied the condition.
    ///
    /// Conditions for correctness:
    /// - `Leaf::Info` should not contain "negative" values so that path-info is non-decreasing when
    ///   `extend`-ed with `Leaf::Info` values.
    ///
    /// See `goto_max` for examples.
    ///
    /// A more descriptive name of this might be `goto_path_suffix_min`.
    pub fn goto_min<PS: SubOrd<PI>>(&mut self, path_info_sub: PS) -> Option<&L> {
        <Self as CursorNav>::goto_min(self, path_info_sub)
    }

    /// Moves the cursor to the last leaf node which satisfy the following condition:
    ///
    /// `path_info_sub >= path_info.extend(node.info())`
    ///
    /// And returns a reference to it. Returns `None` if no leaf satisfied the condition.
    ///
    /// Conditions for correctness is the same as `goto_min`.
    ///
    /// These methods can be visualized as follows:
    ///
    /// ```text
    /// leaf         :     'a'   'b'   'c'   'd'   'e'
    /// leaf::info() :      1     1     1     1     1
    /// path_info    :   0     1     2     3     4     5
    ///     goto_min(3)                    ^--~  ^--~    = first of ('d', 'e') = Some('d')
    ///     goto_max(3)     ~--^  ~--^  ~--^         = last of ('a', 'b', 'c') = Some('c')
    ///     goto_max(0) = None
    ///     goto_min(5) = goto_min(6) = None
    ///     goto_max(5) = goto_max(6) = Some('e')
    ///
    /// =====
    ///
    /// leaf         :     't'   'u'   'v'   'w'   'x'
    /// leaf::info() :      1     1     0     0     1
    /// path_info    :   0     1     2     2     2     3
    ///     goto_min(2)              ^--~  ^--~  ^--~    = first of ('v', 'w', 'x') = Some('v')
    ///     goto_max(2)     ~--^  ~--^  ~--^  ~--^   = last of ('t', 'u', 'v', 'w') = Some('w')
    /// ```
    ///
    /// A more descriptive name of this might be `goto_path_prefix_max`.
    pub fn goto_max<PS: SubOrd<PI>>(&mut self, path_info_sub: PS) -> Option<&L> {
        <Self as CursorNav>::goto_max(self, path_info_sub)
    }
}

impl<L, PI, CONF> CursorNav for CursorMut<L, PI, CONF>
    where L: Leaf,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    type Leaf = L;
    type NodesPtr = CONF::Ptr;
    type PathInfo = PI;

    fn _is_root(&self) -> bool {
        self.is_root()
    }

    fn _path_info(&self) -> PI {
        self.path_info()
    }

    fn _leaf(&self) -> Option<&Self::Leaf> {
        self.leaf()
    }

    fn _height(&self) -> Option<usize> {
        self.height()
    }

    fn _current(&self) -> Option<&Node<L, CONF::Ptr>> {
        self.current()
    }

    fn _current_must(&self) -> &Node<L, CONF::Ptr> {
        &self.cur_node
    }

    fn _reset(&mut self) {
        self.reset();
    }

    fn _ascend(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.ascend()
    }

    fn _descend_first(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.descend_first()
    }

    fn _descend_last(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.descend_last()
    }

    fn _left_sibling(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.left_sibling()
    }

    fn _right_sibling(&mut self) -> Option<&Node<L, CONF::Ptr>> {
        self.right_sibling()
    }
}

// structural modifications
impl<L, PI, CONF> CursorMut<L, PI, CONF>
    where L: Leaf,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    /// Insert `leaf` before or after the current node. If currently not at a leaf node, the cursor
    /// first descends to a leaf node (to the first leaf node if `!after`, or the last leaf node),
    /// and inserts it per `after`.
    ///
    /// It is unspecified where the cursor will be after this operation. But it is guaranteed that
    /// `path_info` will not decrease (i.e. get `extend_inv`-ed). The user should ensure that the
    /// cursor is at the intended location after this.
    pub fn insert_leaf(&mut self, leaf: L, after: bool) {
        self.insert(Node::from_leaf(leaf), after);
    }

    /// Insert `newnode` before or after the current node and rebalance. `newnode` can be of any
    /// height.
    pub fn insert(&mut self, newnode: Node<L, CONF::Ptr>, after: bool) {
        let newnode_ht = newnode.height();
        match self.height() {
            Some(cur_ht) if cur_ht >= newnode_ht => {
                while self.cur_node.height() > newnode_ht {
                    let _res = if after { self.descend_last() } else { self.descend_first() };
                    debug_assert!(_res.is_some());
                }
                return self.insert_simple(newnode, after);
            }
            None => {
                self.cur_node = newnode;
                return;
            }
            _ => (),
        }

        let mut current = self.cur_node.never_take();
        current = if after {
            Node::concat(current, newnode)
        } else {
            Node::concat(newnode, current)
        };

        // TODO investigate possible performance tweaks
        while let Some(CMutStep { mut nodes, idx, path_info, .. }) = self.pop_step() {
            if nodes[(idx + 1) % nodes.len()].height() == current.height() {
                self.push_step(CMutStep::new(nodes, idx, path_info));
                break;
            }

            let nodes = <CONF::Ptr as NodesPtr<L>>::make_mut(&mut nodes);
            let len = nodes.len();

            if idx + 1 < len {
                let right = Node::from_children(
                                <CONF::Ptr as NodesPtr<L>>::new(nodes.drain(idx+1..).collect()));
                current = Node::concat(current, right);
            }

            if idx > 0 {
                let left = Node::from_children(
                               <CONF::Ptr as NodesPtr<L>>::new(nodes.drain(0..idx).collect()));
                current = Node::concat(left, current);
            }
        }
        self.cur_node = current;
    }

    /// Remove the first leaf under the current node.
    pub fn remove_leaf(&mut self) -> Option<L> {
        self.first_leaf();
        self.remove_node().and_then(|n| n.into_leaf().ok())
    }

    /// Remove the current node and return it. If the cursor is empty, return `None`.
    ///
    /// It is unspecified where the cursor will be after this operation. But it is guaranteed that
    /// `path_info` will not increase (or `extend`). The user should ensure that the cursor is at
    /// the correct location after this.
    pub fn remove_node(&mut self) -> Option<Node<L, CONF::Ptr>> {
        match self.take_current() {
            Some(cur_node) => {
                if let Some(mut cstep) = self.pop_step() {
                    let dummy = <CONF::Ptr as NodesPtr<L>>::make_mut(&mut cstep.nodes)
                                    .remove(cstep.idx)
                                    .unwrap();
                    debug_assert!(dummy.is_never());
                    if cstep.nodes.len() > 0 {
                        self.fix_current(cstep);
                    } else {
                        debug_assert!(self.steps.len() == 0); // should be root
                    }
                }
                Some(cur_node)
            },
            None => None, // cursor is empty
        }
    }

    /// Split the tree into two, and return the right part of it. The current node, all leaves
    /// under it, as well as all leaves to the right of it will be included in the returned tree.
    ///
    /// Returns `None` if the cursor was empty.
    ///
    /// Time: O(log n)
    pub fn split_off(&mut self) -> Option<Node<L, CONF::Ptr>> {
        if self.is_empty() {
            return None;
        }

        let mut this = Node::never();
        let mut ret = self.cur_node.never_take();
        // Note on time complexity: Even though time complexity of concat is O(log n), the heights
        // of nodes being concated differ only by 1 (amortized).
        while let Some(CMutStep { mut nodes, idx, .. }) = self.pop_step() {
            { // mutate nodes
                let nodes = <CONF::Ptr as NodesPtr<L>>::make_mut(&mut nodes);
                let right_nodes = nodes.drain(idx + 1 ..)
                                       .collect::<ArrayVec<<CONF::Ptr as NodesPtr<L>>::Array>>();
                if right_nodes.len() > 0 {
                    ret = Node::concat(ret, Node::from_children(
                                                <CONF::Ptr as NodesPtr<L>>::new(right_nodes)));
                }
                nodes.pop(); // pop the never node at idx
            }
            if nodes.len() > 0 {
                let left_node = Node::from_children(nodes);
                this = match this {
                    Node::Never(_) => left_node,
                    _ => Node::concat(left_node, this),
                };
            }
        }

        self.cur_node = this;
        Some(ret)
    }
}

impl<L, PI, CONF> CursorMut<L, PI, CONF>
    where L: Leaf,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    fn insert_simple(&mut self, mut newnode: Node<L, CONF::Ptr>, mut after: bool) {
        if self.is_empty() {
            self.cur_node = newnode;
            return;
        }

        let &mut CursorMut { ref mut cur_node, ref mut steps } = self;
        loop {
            debug_assert_eq!(cur_node.height(), newnode.height());
            match steps.last_mut() {
                Some(&mut CMutStep { ref mut nodes, ref mut idx, ref mut path_info, .. }) => {
                    let maybe_split;
                    {
                        let nodes = <CONF::Ptr as NodesPtr<L>>::make_mut(nodes);

                        if !newnode.has_min_size() {
                            let cur_owned = cur_node.never_take();
                            let (mut children1, mut children2) =
                                if after {
                                    (cur_owned.into_children_must(), newnode.into_children_must())
                                } else {
                                    (newnode.into_children_must(), cur_owned.into_children_must())
                                };
                            let merged = balance_maybe_merge::<_, CONF::Ptr>(
                                <CONF::Ptr as NodesPtr<L>>::make_mut(&mut children1),
                                <CONF::Ptr as NodesPtr<L>>::make_mut(&mut children2));
                            let mut left = Node::from_children(children1);
                            if merged {
                                cur_node.never_swap(&mut left);
                                break;
                            } else {
                                let mut right = Node::from_children(children2);
                                if after {
                                    cur_node.never_swap(&mut left);
                                    newnode = right;
                                } else {
                                    newnode = left;
                                    cur_node.never_swap(&mut right);
                                }
                            }
                        }
                        debug_assert!(!cur_node.is_never());
                        let cur_info = cur_node.info();
                        cur_node.never_swap(&mut nodes[*idx]);
                        if after {
                            *path_info = path_info.extend(cur_info);
                            *idx += 1;
                        }
                        maybe_split = insert_maybe_split(nodes, *idx, newnode);
                    }
                    // now cur_node is never
                    if let Some(split_node) = maybe_split {
                        newnode = split_node;
                        after = true;
                        // the only way out of match without breaking
                    } else {
                        let nodes = <CONF::Ptr as NodesPtr<L>>::make_mut(nodes);
                        cur_node.never_swap(&mut nodes[*idx]);
                        break;
                    }
                }
                None => { // cur_node is the root
                    *cur_node = if after {
                        Node::concat(cur_node.never_take(), newnode)
                    } else {
                        Node::concat(newnode, cur_node.never_take())
                    };
                    break;
                }
            }

            // ascend the tree (cur_node is never, nodes[idx] is valid)
            let CMutStep { nodes, .. } = steps.pop().unwrap();
            let parent = Node::from_children(nodes); // gather info
            *cur_node = parent;
        }
    }

    // Find a replacement node for the current node. May ascend the tree multiple times.
    fn fix_current(&mut self, cstep: CMutStep<L, PI, CONF>) {
        debug_assert!(self.cur_node.is_never());
        let CMutStep { mut nodes, mut idx, mut path_info, .. } = cstep;
        let nodes_len = nodes.len();
        debug_assert!(nodes_len > 0); // nodes should never be empty
        debug_assert!(nodes.iter().all(|n| !n.is_never())); // nodes should be all valid
        let steps_len = self.steps.len();
        if nodes_len >= <CONF::Ptr as NodesPtr<L>>::max_size()/2 || steps_len == 0 {
            let at_right_end = idx == nodes_len;
            if at_right_end {
                idx -= 1;
            }
            self.cur_node.never_swap(&mut <CONF::Ptr as NodesPtr<L>>::make_mut(&mut nodes)[idx]);
            if at_right_end {
                path_info = path_info.extend_inv(self.cur_node.info());
            }
            debug_assert!(self.cur_node.is_leaf() || self.cur_node.has_min_size());
            self.push_step(CMutStep::new(nodes, idx, path_info));
        } else { // steps_len > 0
            debug_assert_eq!(nodes_len, <CONF::Ptr as NodesPtr<L>>::max_size()/2 - 1);
            self.cur_node = Node::from_children(nodes);
            self.merge_adjacent();
        }
    }

    // Merge the current node with an adjacent sibling to make it balanced.
    fn merge_adjacent(&mut self) {
        debug_assert!(!self.cur_node.is_never());
        debug_assert_eq!(self.cur_node.children().len(), <CONF::Ptr as NodesPtr<L>>::max_size()/2 - 1);
        let CMutStep { mut nodes, mut idx, mut path_info, .. } = self.pop_step().unwrap();
        if nodes.len() == 1 { // cur_node is the only child
            debug_assert!(self.steps.len() == 0); // the parent must be root
            return; // cur_node becomes the root
        }
        let merge_left = idx + 1 == nodes.len(); // merge with the right node by default
        debug_assert!(nodes.len() > 1);
        let merged;
        {
            let nodes = <CONF::Ptr as NodesPtr<L>>::make_mut(&mut nodes);
            merged = if merge_left {
                let left_node_int = nodes.get_mut(idx - 1).unwrap().internal_mut_must();
                path_info = path_info.extend_inv(left_node_int.info());
                left_node_int.try_merge_with(self.cur_node.internal_mut_must())
            } else {
                let right_node_int = nodes.get_mut(idx + 1).unwrap().internal_mut_must();
                self.cur_node.internal_mut_must().try_merge_with(right_node_int)
            };
            if merged {
                if merge_left {
                    self.cur_node.never_take(); // make the now empty cur_node never
                    nodes.remove(idx).unwrap(); // and remove its placeholder
                    idx -= 1; // make left_node be the current node (path_info already adjusted)
                } else {
                    nodes.remove(idx + 1).unwrap(); // remove the now empty right_node
                    self.cur_node.never_swap(&mut nodes[idx]);
                }
                debug_assert!(self.cur_node.is_never());
            } else {
                if merge_left {
                    self.cur_node.never_swap(&mut nodes[idx]);
                    idx -= 1; // make left_node be the current node (for path_info correctness)
                    self.cur_node.never_swap(&mut nodes[idx]);
                }
                debug_assert!(!self.cur_node.is_never());
            }
        };
        let cstep = CMutStep::new(nodes, idx, path_info);
        if merged {
            self.fix_current(cstep);
        } else {
            self.push_step(cstep);
        }
    }

    fn ascend_raw(&mut self, mut nodes: CONF::Ptr, idx: usize) {
        debug_assert!(!self.cur_node.is_never());
        self.cur_node.never_swap(&mut <CONF::Ptr as NodesPtr<L>>::make_mut(&mut nodes)[idx]);
        let parent = Node::from_children(nodes); // gather info
        self.cur_node = parent;
    }

    fn descend_raw(&mut self, mut nodes: CONF::Ptr, idx: usize, path_info: PI) {
        debug_assert!(self.cur_node.is_never());
        self.cur_node.never_swap(&mut <CONF::Ptr as NodesPtr<L>>::make_mut(&mut nodes)[idx]);
        self.push_step(CMutStep::new(nodes, idx, path_info));
    }

    fn push_step(&mut self, cstep: CMutStep<L, PI, CONF>) {
        //testln!("descended!");
        let _res = self.steps.push(cstep);
        assert!(_res.is_none(), "Exceeded maximum supported depth.");
    }

    fn pop_step(&mut self) -> Option<CMutStep<L, PI, CONF>> {
        //testln!("ascended! (try)");
        self.steps.pop()
    }

    fn take_current(&mut self) -> Option<Node<L, CONF::Ptr>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref mut cur_node => Some(cur_node.never_take()),
        }
    }
}

impl<L, PI, CONF> FromIterator<L> for CursorMut<L, PI, CONF>
    where L: Leaf,
          PI: PathInfo<L::Info>,
          CONF: CMutConf<L, PI>,
{
    fn from_iter<J: IntoIterator<Item=L>>(iter: J) -> Self {
        let mut curs = CursorMut::new();
        let mut iter = iter.into_iter().map(Node::from_leaf);

        loop {
            let nodes = iter.by_ref()
                            .take(<CONF::Ptr as NodesPtr<L>>::max_size())
                            .collect::<ArrayVec<<CONF::Ptr as NodesPtr<L>>::Array>>();
            if nodes.len() > 0 {
                // TODO investigate `cursormut_insert` benchmark slowdown (git blame this line)
                curs.insert(Node::from_children(<CONF::Ptr as NodesPtr<L>>::new(nodes)), true);
            } else {
                break;
            }
        }
        curs
    }
}

#[cfg(test)]
mod tests {
    use test_help::*;

    type CursorMut<L, PI> = super::CursorMut<L, PI>;

    #[test]
    fn insert() {
        let mut cursor_mut = CursorMutT::new();
        for i in 0..128 {
            cursor_mut.insert_leaf(ListLeaf(i), true);
        }
        let root = cursor_mut.into_root().unwrap();
        let mut leaf_iter = CursorT::new(&root).into_iter();
        for i in 0..128 {
            assert_eq!(leaf_iter.next(), Some(&ListLeaf(i)));
        }
        assert_eq!(leaf_iter.next(), None);
    }

    #[test]
    fn delete() {
        let mut cursor_mut = CursorMutT::new();
        for i in 0..128 {
            cursor_mut.insert_leaf(ListLeaf(i), true);
        }
        cursor_mut.reset();
        for i in 0..128 {
            assert_eq!(cursor_mut.remove_leaf(), Some(ListLeaf(i)));
        }
        assert_eq!(cursor_mut.is_empty(), true);
    }

    #[test]
    fn from_iter() {
        let cursor_mut: CursorMutT<_> = (0..128).map(|i| ListLeaf(i)).collect();
        let root = cursor_mut.into_root().unwrap();
        let mut leaf_iter = CursorT::new(&root).into_iter();
        for i in 0..128 {
            assert_eq!(leaf_iter.next(), Some(&ListLeaf(i)));
        }
        assert_eq!(leaf_iter.next(), None);
    }

    #[test]
    fn root_balance() {
        let mut cursor_mut: CursorMutT<_> = (0..2).map(|i| ListLeaf(i)).collect();
        cursor_mut.remove_leaf();
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(1)); // allow root with single leaf child

        let mut cursor_mut: CursorMutT<_> = (0..17).map(|i| ListLeaf(i)).collect();
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(2));
        cursor_mut.descend_first();
        cursor_mut.remove_node(); // now root has only one child
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(2));
        cursor_mut.remove_leaf();
        cursor_mut.remove_leaf();
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(1));
    }

    #[test]
    fn node_iter() {
        let mut cursor_mut: CursorMutT<_> = (0..128).map(|i| ListLeaf(i)).collect();
        cursor_mut.reset();
        assert_eq!(cursor_mut.first_leaf(), Some(&ListLeaf(0)));
        for i in 1..128 {
            assert_eq!(cursor_mut.next_node().and_then(|n| n.leaf()), Some(&ListLeaf(i)));
        }
        assert_eq!(cursor_mut.next_node().and_then(|n| n.leaf()), None);
    }

    #[test]
    fn find_min_max() {
        let rand = || rand_usize(256) + 4;
        let (l1, l2, l3) = (rand(), rand(), rand());
        println!("lengths: {:?}", (l1, l2, l3));

        let mut cursor_mut: CursorMutT<_> =        (0..l1).map(|i| SetLeaf('b', i))
                                            .chain((0..l2).map(|i| SetLeaf('c', i)))
                                            .chain((0..l3).map(|i| SetLeaf('d', i)))
                                            .collect();

        assert_eq!(cursor_mut.find_min(MinChar('a')), Some(&SetLeaf('b', 0)));
        assert_eq!(cursor_mut.find_min(MinChar('b')), Some(&SetLeaf('b', 0)));
        assert_eq!(cursor_mut.find_min(MinChar('c')), Some(&SetLeaf('c', 0)));
        assert_eq!(cursor_mut.find_min(MinChar('d')), Some(&SetLeaf('d', 0)));
        assert_eq!(cursor_mut.find_min(MinChar('e')), None);

        assert_eq!(cursor_mut.find_max(MaxChar('a')), None);
        assert_eq!(cursor_mut.find_max(MaxChar('b')), Some(&SetLeaf('b', l1-1)));
        assert_eq!(cursor_mut.find_max(MaxChar('c')), Some(&SetLeaf('c', l2-1)));
        assert_eq!(cursor_mut.find_max(MaxChar('d')), Some(&SetLeaf('d', l3-1)));
        assert_eq!(cursor_mut.find_max(MaxChar('e')), Some(&SetLeaf('d', l3-1)));

        let leaf = SetLeaf('b', rand_usize(8));
        assert_eq!(cursor_mut.find_min(MinLeaf(leaf)), Some(&leaf));
        assert_eq!(cursor_mut.find_max(MaxLeaf(leaf)), Some(&leaf));
    }

    #[test]
    fn goto_min_max() {
        let mut cursor_mut: CursorMut<_, ListPath> = (0..128).map(|i| ListLeaf(i)).collect();
        assert_eq!(cursor_mut.goto_min(ListIndex(50)), Some(&ListLeaf(50)));
        assert_eq!(cursor_mut.goto_min(ListRun(79*80/2)), Some(&ListLeaf(80)));
        cursor_mut.reset();
        assert_eq!(cursor_mut.goto_max(ListIndex(50)), Some(&ListLeaf(49)));
        assert_eq!(cursor_mut.goto_max(ListRun(79*80/2)), Some(&ListLeaf(79)));

        let mut cursor_mut: CursorMut<_, ListPath> = vec![2, 1, 0, 0, 0, 3, 4].into_iter()
                                                         .map(|i| ListLeaf(i)).collect();
        assert_eq!(cursor_mut.goto_min(ListRun(3)), Some(&ListLeaf(0)));
        assert_eq!(cursor_mut.prev_leaf(), Some(&ListLeaf(1)));
        assert_eq!(cursor_mut.goto_max(ListRun(3)), Some(&ListLeaf(0)));
        assert_eq!(cursor_mut.next_leaf(), Some(&ListLeaf(3)));
    }

    #[test]
    fn split_off() {
        let total = rand_usize(2048) + 1;
        let split_at = rand_usize(total);
        println!("total: {}, split_at: {}", total, split_at);

        let mut cursor_mut: CursorMutT<_> = (0..total).map(|i| SetLeaf('a', i)).collect();
        cursor_mut.reset();

        let orig_ht = cursor_mut.height().unwrap();

        cursor_mut.find_min(MinLeaf(SetLeaf('a', split_at))).unwrap();

        let right = cursor_mut.split_off().unwrap();
        let mut leaf_iter = CursorT::new(&right).into_iter();
        for i in split_at..total {
            assert_eq!(leaf_iter.next(), Some(&SetLeaf('a', i)));
        }

        let left = cursor_mut.into_root().unwrap();
        let mut leaf_iter = CursorT::new(&left).into_iter();
        for i in 0..split_at {
            assert_eq!(leaf_iter.next(), Some(&SetLeaf('a', i)));
        }

        let (left_ht, right_ht) = (left.height(), right.height());
        println!("heights, orig: {}, left: {}, right: {}", orig_ht, left_ht, right_ht);
        assert!((orig_ht == left_ht || orig_ht == right_ht) &&
                (orig_ht >= left_ht && orig_ht >= right_ht));
    }

    #[test]
    fn general_insert() {
        let rand = || rand_usize(256) + 4;
        let (l1, l2, l3) = (rand(), rand(), rand());
        println!("lengths: {:?}", (l1, l2, l3));
        let mut cursor_mut: CursorMutT<_> =        (0..l1).map(|i| SetLeaf('a', i))
                                            .chain((0..l3).map(|i| SetLeaf('a', l1 + l2 + i)))
                                            .collect();
        cursor_mut.reset();

        cursor_mut.find_min(MinLeaf(SetLeaf('a', l1))).unwrap();

        let node: NodeRc<_> = (0..l2).map(|i| SetLeaf('a', l1 + i)).collect();
        cursor_mut.insert(node, false);
        cursor_mut.reset();

        let mut leaf_iter = CursorT::new(cursor_mut.current().unwrap()).into_iter();
        for i in 0..l1+l2+l3 {
            assert_eq!(leaf_iter.next(), Some(&SetLeaf('a', i)));
        }
    }

    // FIXME need more tests (create verify_balanced function?)
}
