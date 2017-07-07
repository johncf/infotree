use ::{CVec, NVec, RC};
use ::{MAX_CHILDREN, MIN_CHILDREN};
use base::Node;
use traits::{Leaf, PathInfo, SubOrd};
use node::{insert_maybe_split, balance_maybe_merge};

use std::fmt;
use std::iter::FromIterator;

// Note: The working of `CursorMut` is fundamentally different from `Cursor`. `CursorMut` can
//       become empty (iff `cur_node` is empty. `cur_node` empty implies `steps` is also empty).

/// A object that can be used to modify internals of `Node` while maintaining balance.
///
/// `CursorMut` is heavier compared to `Cursor`. Even though `CursorMut` does not make any heap
/// allocations for its own operations, most operations tries to make the current node writable
/// using `Arc::make_mut`. This could result in a heap allocation if the number of references to
/// that node is more than one.
///
/// Note: `CursorMut` takes more than 200B on stack (exact size mainly depends on the size of `P`)
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

    /// Returns a reference to the leaf's value if the current node is a leaf.
    pub fn leaf(&self) -> Option<&L> {
        match self.cur_node {
            Node::Never(_) => None,
            ref cur_node => cur_node.leaf(),
        }
    }

    /// Update the leaf value in-place using `f`. This is a no-op if the current node is not a
    /// leaf.
    pub fn leaf_update<F>(&mut self, f: F) where F: FnOnce(&mut L) {
        self.cur_node.leaf_update(f);
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

enum FindStatus {
    HitRoot, // condition was false at root
    HitTrue, // condition was true at its pibling
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
                Some(&self.cur_node)
            }
            None => { // cur_node is the root (or empty)
                None
            }
        }
    }

    pub fn descend_first(&mut self) -> Option<&Node<L>> {
        self.descend_by(|_, _, _, _| true, false)
    }

    pub fn descend_last(&mut self) -> Option<&Node<L>> {
        self.descend_by(|_, _, _, _| true, true)
    }

    pub fn first_leaf(&mut self) -> Option<&L> {
        self.descend_first_till(|_, _, _| false);
        self.leaf()
    }

    pub fn last_leaf(&mut self) -> Option<&L> {
        self.descend_last_till(|_, _, _| false);
        self.leaf()
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

    pub fn ascend_till(&mut self, height: usize) -> Option<&Node<L>> {
        while let Some(ht) = self.height() {
            if ht == height { return self.current(); }
            else if ht + 1 == height { return self.ascend(); }
            else if ht + 1 < height { self.ascend(); }
            else { break; }
        }
        return None;
    }

    pub fn left_sibling(&mut self) -> Option<&Node<L>> {
        let &mut CursorMut { ref mut cur_node, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CursorMutStep { ref mut nodes, ref mut idx, ref mut path_info }) => {
                debug_assert!(!cur_node.is_never());
                if *idx > 0 {
                    let nodes = RC::make_mut(nodes);
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

    pub fn right_sibling(&mut self) -> Option<&Node<L>> {
        let &mut CursorMut { ref mut cur_node, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CursorMutStep { ref mut nodes, ref mut idx, ref mut path_info }) => {
                debug_assert!(!cur_node.is_never());
                if *idx + 1 < nodes.len() {
                    *path_info = path_info.extend(cur_node.info());

                    let nodes = RC::make_mut(nodes);
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

    /// Tries to return the sibling on the left if exists, or ascends the tree until an ancestor
    /// with a left sibling is found and returns that sibling. (Note: "pibling" as in parent's
    /// sibling)
    pub fn left_sibling_or_pibling(&mut self) -> Option<&Node<L>> {
        loop {
            match self.left_sibling() {
                Some(_) => return Some(&self.cur_node),
                None => {
                    match self.ascend() {
                        Some(_) => (),
                        None => return None,
                    }
                }
            }
        }
    }

    pub fn right_sibling_or_pibling(&mut self) -> Option<&Node<L>> {
        loop {
            match self.right_sibling() {
                Some(_) => return Some(&self.cur_node),
                None => {
                    match self.ascend() {
                        Some(_) => (),
                        None => return None,
                    }
                }
            }
        }
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
    /// - `L::Info::gather` must apply the "min" function on this field.
    ///
    /// See `find_max` for examples.
    pub fn find_min<IS: SubOrd<L::Info>>(&mut self, info_sub: IS) -> Option<&L> {
        use std::cmp::Ordering;

        let satisfies = |info: L::Info| -> bool {
            match info_sub.sub_cmp(&info) {
                Ordering::Less | Ordering::Equal => true,
                Ordering::Greater => false,
            }
        };

        let mut status;
        // ascend till a well-defined state
        match self.current().map(|n| satisfies(n.info())) {
            Some(true) => {
                if !self.left_ascend_till(|_, info| !satisfies(info)) {
                    // condition is satisfied at root
                    return self.first_leaf(); // must unwrap
                }
                status = FindStatus::HitTrue;
            },
            Some(false) => {
                if self.right_ascend_till(|_, info| satisfies(info)) {
                    self.left_sibling(); // make condition false, must unwrap
                    status = FindStatus::HitTrue;
                } else {
                    status = FindStatus::HitRoot;
                }
            },
            None => return None,
        }

        debug_assert!(!satisfies(self.current().unwrap().info()));

        // descend till the last leaf that don't satisfy the condition
        loop {
            if self.descend_last_till(|_, info, _| satisfies(info)) {
                // find the sibling that don't satisfy the condition
                while let Some(true) = self.left_sibling().map(|n| satisfies(n.info())) {}
                status = FindStatus::HitTrue;
            } else {
                break;
            }
        }

        debug_assert!(self.leaf().is_some());
        debug_assert!(!satisfies(self.current().unwrap().info()));

        match status {
            FindStatus::HitRoot => None,
            FindStatus::HitTrue => self.next_node().and_then(|n| n.leaf()), // must unwrap
        }
    }

    /// Moves the cursor to the last leaf node which satisfy the following condition:
    ///
    /// `info_sub >= node.info()`
    ///
    /// And returns a reference to it. Returns `None` if no leaf satisfied the condition.
    ///
    /// Conditions for correctness is the same as `find_min`, except that `L::Info::gather` must
    /// apply the "max" function on this field, instead of "min".
    ///
    /// Note: If exactly one leaf satisfies equality with `info_sub`, then both `find_max` and
    /// `find_min` will return the same element. Here are some examples:
    /// ```text
    /// leaf:     ('c', 2)   ('j', 1)   ('j', 4)   ('v', 2)
    /// find_min('j') == Some(('j', 1))
    /// find_max('j') == find_max('k') == Some(('j', 4))
    /// find_min('k') == find_max('z') == Some(('v', 2))
    /// find_min('z') == find_max('a') == None
    /// ```
    pub fn find_max<IS: SubOrd<L::Info>>(&mut self, info_sub: IS) -> Option<&L> {
        use std::cmp::Ordering;

        let satisfies = |info: L::Info| -> bool {
            match info_sub.sub_cmp(&info) {
                Ordering::Greater | Ordering::Equal => true,
                Ordering::Less => false,
            }
        };

        let mut status;
        // ascend till a well-defined state
        match self.current().map(|n| satisfies(n.info())) {
            Some(true) => {
                if !self.right_ascend_till(|_, info| !satisfies(info)) {
                    // condition is satisfied at root
                    return self.last_leaf(); // must unwrap
                }
                status = FindStatus::HitTrue;
            },
            Some(false) => {
                if self.left_ascend_till(|_, info| satisfies(info)) {
                    self.right_sibling(); // make condition false, must unwrap
                    status = FindStatus::HitTrue;
                } else {
                    status = FindStatus::HitRoot;
                }
            },
            None => return None,
        }

        debug_assert!(!satisfies(self.current().unwrap().info()));

        // descend till the first leaf that don't satisfy the condition
        loop {
            if self.descend_first_till(|_, info, _| satisfies(info)) {
                // find the sibling that don't satisfy the condition
                while let Some(true) = self.right_sibling().map(|n| satisfies(n.info())) {}
                status = FindStatus::HitTrue;
            } else {
                break;
            }
        }

        debug_assert!(self.leaf().is_some());
        debug_assert!(!satisfies(self.current().unwrap().info()));

        match status {
            FindStatus::HitRoot => None,
            FindStatus::HitTrue => self.prev_node().and_then(|n| n.leaf()), // must unwrap
        }
    }

    /// Moves the cursor to the first leaf node which satisfy the following condition:
    ///
    /// `path_info_sub <= path_info.extend(node.info())`
    ///
    /// And returns a reference to it. Returns `None` if no leaf satisfied the condition.
    ///
    /// Conditions for correctness:
    /// - `L::Info` should not contain "negative" values so that path-info is non-decreasing when
    ///   `extend`-ed with `L::Info` values.
    ///
    /// See `goto_max` for examples.
    pub fn goto_min<PS: SubOrd<P>>(&mut self, _path_info_sub: PS) -> Option<&L> {
        unimplemented!()
    }

    /// Moves the cursor to the last leaf node which satisfy the following condition:
    ///
    /// `path_info <= path_info_sub`
    ///
    /// And returns a reference to it. Returns `None` if no leaf satisfied the condition.
    ///
    /// Conditions for correctness is the same as `goto_min`.
    ///
    /// Note: Both of these methods can be visualized as follows:
    /// ```text
    /// leaf         :     'a'   'b'   'c'   'd'   'e'
    /// leaf::info() :      1     1     1     1     1
    /// path_info    :   0     1     2  ^  3  ^  4     5
    ///                                 ^--------------- goto_min(3) = first of ('c', 'd', 'e')
    ///      goto_max(3) ---------------------^ = last of ('a', 'b', 'c', 'd')
    /// ```
    /// That is, for any `p: PS`, `goto_min(p) <= goto_max(p)`. Below are a few more examples:
    /// ```text
    /// goto_min(0) == goto_min(1) == Some('a')
    /// goto_max(4) == goto_max(5) == goto_max(6) == Some('e')
    /// goto_min(6) == None
    /// ```
    pub fn goto_max<PS: SubOrd<P>>(&mut self, _path_info_sub: PS) -> Option<&L> {
        unimplemented!()
    }

    /// Make the cursor point to the next element at the same height.
    ///
    /// If there is no next element, it returns `None` and cursor resets to root.
    pub fn next_node(&mut self) -> Option<&Node<L>> {
        let mut depth_delta = 0;
        loop {
            match self.right_sibling() {
                Some(_) => {
                    while depth_delta > 0 {
                        self.descend_first().unwrap();
                        depth_delta -= 1;
                    }
                    return Some(&self.cur_node);
                }
                None => {
                    match self.ascend() {
                        Some(_) => depth_delta += 1,
                        None => return None,
                    }
                }
            }
        }
    }

    /// Make the cursor point to the previous element at the same height.
    ///
    /// If there is no previous element, it returns `None` and cursor resets to root.
    pub fn prev_node(&mut self) -> Option<&Node<L>> {
        let mut depth_delta = 0;
        loop {
            match self.left_sibling() {
                Some(_) => {
                    while depth_delta > 0 {
                        self.descend_last().unwrap();
                        depth_delta -= 1;
                    }
                    return Some(&self.cur_node);
                }
                None => {
                    match self.ascend() {
                        Some(_) => depth_delta += 1,
                        None => return None,
                    }
                }
            }
        }
    }
}

// structural modifications
impl<L, P> CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    /// Insert `leaf` before or after the current node. If currently not at a leaf node, the cursor
    /// first descends to a leaf node (first leaf node if `after == false`, or last leaf node), and
    /// inserts it before or after it.
    ///
    /// It is unspecified where the cursor will be after this operation. But it is guaranteed that
    /// `path_info` will not decrease (or `extend_inv`). The user should ensure that the cursor is
    /// at the intended location after this.
    pub fn insert_leaf(&mut self, leaf: L, after: bool) {
        self.insert(Node::from_leaf(leaf), after);
    }

    /// Insert `node` before or after the current node and rebalance. `node` can be of any height.
    pub fn insert(&mut self, newnode: Node<L>, after: bool) {
        let newnode_ht = newnode.height();
        match self.height() {
            Some(cur_ht) if cur_ht == newnode_ht => {
                return self.insert_simple(newnode, after);
            }
            Some(cur_ht) if cur_ht > newnode_ht => {
                if after {
                    self.descend_last_till(|_, _, ht| ht == newnode_ht);
                } else {
                    self.descend_first_till(|_, _, ht| ht == newnode_ht);
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
        while let Some(CursorMutStep { mut nodes, idx, path_info }) = self.steps.pop() {
            if nodes[(idx + 1) % nodes.len()].height() == current.height() {
                self.steps.push(CursorMutStep { nodes, idx, path_info });
                break;
            }

            let nodes = RC::make_mut(&mut nodes);
            let len = nodes.len();

            if idx + 1 < len {
                let right = Node::from_children(RC::new(nodes.drain(idx+1..).collect()));
                current = Node::concat(current, right);
            }

            if idx > 0 {
                let left = Node::from_children(RC::new(nodes.drain(0..idx).collect()));
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

    /// Split the tree into two, and return the right part of it. The current node, all leaves
    /// under it, as well as all leaves to the right of it will be included in the returned tree.
    ///
    /// Returns `None` if the cursor was empty.
    ///
    /// Time: O(log n)
    pub fn split_off(&mut self) -> Option<Node<L>> {
        if self.is_empty() {
            return None;
        }

        let mut this = Node::never();
        let mut ret = self.cur_node.never_take();
        // Note on time complexity: Even though time complexity of concat is O(log n), the heights
        // of nodes being concated differ only by 1 (amortized).
        while let Some(CursorMutStep { mut nodes, idx, .. }) = self.steps.pop() {
            { // mutate nodes
                let nodes = RC::make_mut(&mut nodes);
                let right_nodes: NVec<_> = nodes.drain(idx + 1 ..).collect();
                if right_nodes.len() > 0 {
                    ret = Node::concat(ret, Node::from_children(RC::new(right_nodes)));
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

impl<L, P> CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    // Returns `Some(node)` if `predicate` was true for some node while descending on the first
    // child. Returns `None` if `predicate` was never true. Descends atleast once.
    fn descend_first_till<F>(&mut self, predicate: F) -> bool
        where F: Fn(P, L::Info, usize) -> bool
    {
        loop {
            let path_info = self.path_info();
            match self.descend_first().map(|n| predicate(path_info, n.info(), n.height())) {
                Some(true) => return true,
                Some(false) => (),
                None => return false,
            }
        }
    }

    // Returns `Some(node)` if `predicate` was true for some node while descending on the last
    // child. Returns `None` if `predicate` was never true. Descends atleast once.
    fn descend_last_till<F>(&mut self, predicate: F) -> bool
        where F: Fn(P, L::Info, usize) -> bool
    {
        loop {
            let path_info = self.path_info();
            match self.descend_last().map(|n| predicate(path_info, n.info(), n.height())) {
                Some(true) => return true,
                Some(false) => (),
                None => return false,
            }
        }
    }

    // Calls `left_sibling_or_pibling` until `predicate` is `true`. Returns `false` if root was
    // reached and `predicate` is still `false`. Ascends atleast once.
    fn left_ascend_till<F>(&mut self, predicate: F) -> bool
        where F: Fn(P, L::Info) -> bool
    {
        loop {
            let path_info = self.path_info();
            match self.left_sibling_or_pibling().map(|n| predicate(path_info, n.info())) {
                Some(true) => return true,
                Some(false) => (),
                None => return false,
            }
        }
    }

    // Calls `right_sibling_or_pibling` until `predicate` is `true`. Returns `false` if root was
    // reached and `predicate` is still `false`. Ascends atleast once.
    fn right_ascend_till<F>(&mut self, predicate: F) -> bool
        where F: Fn(P, L::Info) -> bool
    {
        loop {
            let path_info = self.path_info();
            match self.right_sibling_or_pibling().map(|n| predicate(path_info, n.info())) {
                Some(true) => return true,
                Some(false) => (),
                None => return false,
            }
        }
    }

    fn insert_simple(&mut self, mut newnode: Node<L>, mut after: bool) {
        if self.is_empty() {
            self.cur_node = newnode;
            return;
        }

        let &mut CursorMut { ref mut cur_node, ref mut steps } = self;
        loop {
            debug_assert_eq!(cur_node.height(), newnode.height());
            match steps.last_mut() {
                Some(&mut CursorMutStep { ref mut nodes, ref mut idx, ref mut path_info }) => {
                    let maybe_split = {
                        let nodes = RC::make_mut(nodes);
                        let cur_info = cur_node.info();
                        cur_node.never_swap(&mut nodes[*idx]);
                        if after {
                            *path_info = path_info.extend(cur_info);
                            *idx += 1;
                        }
                        insert_maybe_split(nodes, *idx, newnode)
                    };
                    // now cur_node is never <=> !self.is_empty & assertion in never_swap
                    if let Some(split_node) = maybe_split {
                        newnode = split_node;
                        after = true;
                        // the only way out of match without breaking
                    } else {
                        cur_node.never_swap(&mut RC::make_mut(nodes)[*idx]);
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
            let CursorMutStep { nodes, .. } = steps.pop().unwrap();
            let parent = Node::from_children(nodes); // gather info
            *cur_node = parent;
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
            self.cur_node.never_swap(&mut RC::make_mut(&mut nodes)[idx]);
            debug_assert!(self.cur_node.children().len() == 0 ||
                          self.cur_node.children().len() >= MIN_CHILDREN);
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
        debug_assert_eq!(self.cur_node.children().len(), MIN_CHILDREN - 1);
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
                    self.cur_node.never_swap(&mut nodes[idx]);
                }
                debug_assert!(self.cur_node.is_never());
            } else {
                if at_right_end {
                    self.cur_node.never_swap(&mut nodes[idx]);
                    idx -= 1; // make left_node be the current node (for path_info correctness)
                    self.cur_node.never_swap(&mut nodes[idx]);
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
        self.cur_node.never_swap(&mut RC::make_mut(&mut nodes)[idx]);
        let parent = Node::from_children(nodes); // gather info
        self.cur_node = parent;
    }

    fn descend_raw(&mut self, mut nodes: RC<NVec<Node<L>>>, idx: usize, path_info: P) {
        debug_assert!(self.cur_node.is_never());
        self.cur_node.never_swap(&mut RC::make_mut(&mut nodes)[idx]);
        let _res = self.steps.push(CursorMutStep { nodes, idx, path_info });
        assert!(_res.is_none(), "Exceeded maximum supported depth.");
    }

    fn take_current(&mut self) -> Option<Node<L>> {
        match self.cur_node {
            Node::Never(_) => None,
            ref mut cur_node => Some(cur_node.never_take()),
        }
    }
}

impl<L, P> FromIterator<L> for CursorMut<L, P> where L: Leaf, P: PathInfo<L::Info> {
    fn from_iter<J: IntoIterator<Item=L>>(iter: J) -> Self {
        let mut curs = CursorMut::new();
        let mut iter = iter.into_iter().map(|e| Node::from_leaf(e));

        loop {
            let nodes: NVec<_> = iter.by_ref().take(MAX_CHILDREN).collect();
            if nodes.len() > 0 {
                // TODO investigate `cursormut_insert` benchmark slowdown (git blame this line)
                curs.insert(Node::from_children(RC::new(nodes)), true);
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
    use ::base::Node;
    use ::test_help::*;

    type CursorMutT<L> = CursorMut<L, ()>;

    #[test]
    fn insert() {
        let mut cursor_mut = CursorMutT::new();
        for i in 0..128 {
            cursor_mut.insert_leaf(TestLeaf(i), true);
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
            cursor_mut.insert_leaf(TestLeaf(i), true);
        }
        cursor_mut.reset();
        for i in 0..128 {
            assert_eq!(cursor_mut.remove_leaf(), Some(TestLeaf(i)));
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
        cursor_mut.remove_leaf();
        cursor_mut.reset();
        assert_eq!(cursor_mut.height(), Some(1)); // allow root with single leaf child

        let mut cursor_mut: CursorMutT<_> = (0..17).map(|i| TestLeaf(i)).collect();
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
        let mut cursor_mut: CursorMutT<_> = (0..128).map(|i| TestLeaf(i)).collect();
        cursor_mut.reset();
        assert_eq!(cursor_mut.first_leaf(), Some(&TestLeaf(0)));
        for i in 1..128 {
            assert_eq!(cursor_mut.next_node().and_then(|n| n.leaf()), Some(&TestLeaf(i)));
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
    fn split_off() {
        let total = rand_usize(2048) + 1;
        let split_at = rand_usize(total);
        println!("total: {}, split_at: {}", total, split_at);

        let mut cursor_mut: CursorMutT<_> = (0..total).map(|i| SetLeaf('a', i)).collect();
        cursor_mut.reset();

        let orig_ht = cursor_mut.height().unwrap();

        cursor_mut.find_min(MinLeaf(SetLeaf('a', split_at))).unwrap();

        let right = cursor_mut.split_off().unwrap();
        let mut cursor = CursorT::new(&right);
        for i in split_at..total {
            assert_eq!(cursor.next_leaf(), Some(&SetLeaf('a', i)));
        }

        let left = cursor_mut.into_root().unwrap();
        let mut cursor = CursorT::new(&left);
        for i in 0..split_at {
            assert_eq!(cursor.next_leaf(), Some(&SetLeaf('a', i)));
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

        let node: Node<_> = (0..l2).map(|i| SetLeaf('a', l1 + i)).collect();
        cursor_mut.insert(node, false);
        cursor_mut.reset();

        let mut cursor = CursorT::new(&cursor_mut.current().unwrap());
        for i in 0..l1+l2+l3 {
            assert_eq!(cursor.next_leaf(), Some(&SetLeaf('a', i)));
        }
    }

    // FIXME need more tests (create verify_balanced function?)
}
