use base::Node;
use traits::{Leaf, PathInfo, SubOrd};
use actions::{NodeAction, LeafAction};

pub trait CursorNav: Sized {
    type Leaf: Leaf;
    type PathInfo: PathInfo<<Self::Leaf as Leaf>::Info>;

    /// Returns whether the cursor is currently at the root of the tree.
    fn is_root(&self) -> bool;

    /// The cumulative info along the path from root to this node. Returns `PathInfo::identity()`
    /// if the current node is root or cursor is empty.
    fn path_info(&self) -> Self::PathInfo;

    #[doc(hidden)]
    fn _leaf(&self) -> Option<&Self::Leaf>;
    #[doc(hidden)]
    fn _height(&self) -> Option<usize>;
    #[doc(hidden)]
    fn _current(&self) -> Option<&Node<Self::Leaf>>;
    #[doc(hidden)]
    fn _current_must(&self) -> &Node<Self::Leaf>;

    fn reset(&mut self);
    fn ascend(&mut self) -> Option<&Node<Self::Leaf>>;
    fn descend_first(&mut self) -> Option<&Node<Self::Leaf>>;
    fn descend_last(&mut self) -> Option<&Node<Self::Leaf>>;
    fn left_sibling(&mut self) -> Option<&Node<Self::Leaf>>;
    fn right_sibling(&mut self) -> Option<&Node<Self::Leaf>>;

    fn first_leaf(&mut self) -> Option<&Self::Leaf> {
        while self.descend_first().is_some() {}
        self._leaf()
    }

    fn last_leaf(&mut self) -> Option<&Self::Leaf> {
        while self.descend_last().is_some() {}
        self._leaf()
    }

    /// Make the cursor point to the next element at the same height.
    ///
    /// If there is no next element, it returns `None` and cursor resets to root.
    fn next_node(&mut self) -> Option<&Node<Self::Leaf>> {
        let height = self._height();
        if self.right_maybe_ascend().is_some() {
            let height = height.unwrap();
            while self._current_must().height() > height {
                let _res = self.descend_first();
                debug_assert!(_res.is_some());
            }
            Some(&self._current_must())
        } else {
            None
        }
    }

    /// Make the cursor point to the previous element at the same height.
    ///
    /// If there is no previous element, it returns `None` and cursor resets to root.
    fn prev_node(&mut self) -> Option<&Node<Self::Leaf>> {
        let height = self._height();
        if self.left_maybe_ascend().is_some() {
            let height = height.unwrap();
            while self._current_must().height() > height {
                let _res = self.descend_last();
                debug_assert!(_res.is_some());
            }
            Some(self._current_must())
        } else {
            None
        }
    }

    /// Calls `next_node` and returns the leaf value if it is a leaf node.
    fn next_leaf(&mut self) -> Option<&Self::Leaf> {
        self.next_node().and_then(|n| n.leaf())
    }

    /// Calls `prev_node` and returns the leaf value if it is a leaf node.
    fn prev_leaf(&mut self) -> Option<&Self::Leaf> {
        self.prev_node().and_then(|n| n.leaf())
    }

    /// Tries to return the left sibling if exists, or ascends the tree until an ancestor with a
    /// left sibling is found and returns that sibling.
    fn left_maybe_ascend(&mut self) -> Option<&Node<Self::Leaf>> {
        loop {
            if self.left_sibling().is_some() {
                return Some(self._current_must());
            } else if self.ascend().is_none() {
                return None;
            }
        }
    }

    /// Tries to return the right sibling if exists, or ascends the tree until an ancestor with a
    /// right sibling is found and returns that sibling.
    fn right_maybe_ascend(&mut self) -> Option<&Node<Self::Leaf>> {
        loop {
            if self.right_sibling().is_some() {
                return Some(self._current_must());
            } else if self.ascend().is_none() {
                return None;
            }
        }
    }

    /// Calls the action associated with `A` until `predicate` is `true` and returns `true` if did.
    /// Returns `false` if `predicate` was never true. Calls the action atleast once.
    fn action_till<A, F>(&mut self, predicate: F) -> bool
        where A: actions::NodeAction,
              F: Fn(Self::PathInfo, <Self::Leaf as Leaf>::Info) -> bool
    {
        while A::act_on(self).is_some() {
            if predicate(self.path_info(), self._current_must().info()) {
                return true;
            }
        }
        return false;
    }

    #[doc(hidden)]
    fn jump_to<JAS, F>(&mut self, satisfies: F) -> Option<&Self::Leaf>
        where JAS: actions::JumpActionSet,
              F: Fn(Self::PathInfo, <Self::Leaf as Leaf>::Info) -> bool,
    {
        enum FindStatus {
            HitRoot, // condition was false at root
            HitTrue, // condition was true at its pibling
        }

        let mut status;
        // ascend till a well-defined state
        match self._current().map(|n| satisfies(self.path_info(), n.info())) {
            Some(true) => {
                if !self.action_till::<JAS::AscendToFalse, _>(|path_info, info| !satisfies(path_info, info)) {
                    // condition is satisfied at root
                    return JAS::TrueRootToLeaf::act_on(self); // must unwrap
                }
                status = FindStatus::HitTrue;
            },
            Some(false) => {
                if self.is_root() {
                    status = FindStatus::HitRoot;
                } else {
                    if self.action_till::<JAS::AscendToTrue, _>(|path_info, info| satisfies(path_info, info)) {
                        JAS::SiblingToFalse::act_on(self); // make condition false, must unwrap
                        status = FindStatus::HitTrue;
                    } else {
                        status = FindStatus::HitRoot;
                    }
                }
            },
            None => return None,
        }

        debug_assert!(!satisfies(self.path_info(), self._current().unwrap().info()));

        // descend till the last leaf that don't satisfy the condition
        while self.action_till::<JAS::DescendToFalse, _>(|path_info, info| satisfies(path_info, info)) {
            status = FindStatus::HitTrue;
            if !self.action_till::<JAS::SiblingToFalse, _>(|path_info, info| !satisfies(path_info, info)) {
                // there must be a sibling that don't satisfy the condition
                unreachable!();
            }
        }

        debug_assert!(self._leaf().is_some());
        debug_assert!(!satisfies(self.path_info(), self._current().unwrap().info()));

        match status {
            FindStatus::HitRoot => None,
            FindStatus::HitTrue => JAS::FalseLeafToTrue::act_on(self), // must unwrap
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
    /// - `Leaf::Info::gather` must apply the "min" function on this field.
    ///
    /// See `find_max` for examples.
    ///
    /// A more descriptive name of this might be `find_sorted_suffix_min`.
    fn find_min<IS>(&mut self, info_sub: IS) -> Option<&Self::Leaf>
        where IS: SubOrd<<Self::Leaf as Leaf>::Info>,
    {
        use std::cmp::Ordering;

        let satisfies = |_path_info, info| -> bool {
            match info_sub.sub_cmp(&info) {
                Ordering::Less | Ordering::Equal => true,
                Ordering::Greater => false,
            }
        };

        self.jump_to::<actions::PrefixMin, _>(satisfies)
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
    fn find_max<IS>(&mut self, info_sub: IS) -> Option<&Self::Leaf>
        where IS: SubOrd<<Self::Leaf as Leaf>::Info>,
    {
        use std::cmp::Ordering;

        let satisfies = |_path_info, info| -> bool {
            match info_sub.sub_cmp(&info) {
                Ordering::Greater | Ordering::Equal => true,
                Ordering::Less => false,
            }
        };

        self.jump_to::<actions::SuffixMax, _>(satisfies)
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
    fn goto_min<PS: SubOrd<Self::PathInfo>>(&mut self, path_info_sub: PS) -> Option<&Self::Leaf> {
        use std::cmp::Ordering;

        let satisfies = |path_info, _info| -> bool {
            match path_info_sub.sub_cmp(&path_info) {
                Ordering::Less | Ordering::Equal => true,
                Ordering::Greater => false,
            }
        };

        self.jump_to::<actions::PrefixMin, _>(satisfies)
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
    fn goto_max<PS: SubOrd<Self::PathInfo>>(&mut self, path_info_sub: PS) -> Option<&Self::Leaf> {
        use std::cmp::Ordering;

        let satisfies = |path_info: Self::PathInfo, info| -> bool {
            match path_info_sub.sub_cmp(&path_info.extend(info)) {
                Ordering::Greater | Ordering::Equal => true,
                Ordering::Less => false,
            }
        };

        self.jump_to::<actions::SuffixMax, _>(satisfies)
    }
}

pub mod actions {
    use super::{CursorNav, Node};

    pub trait NodeAction {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf>>;
    }

    pub trait LeafAction {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&C::Leaf>;
    }

    pub enum LeftSibling {}
    impl NodeAction for LeftSibling {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf>> {
            cursor.left_sibling()
        }
    }

    pub enum RightSibling {}
    impl NodeAction for RightSibling {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf>> {
            cursor.right_sibling()
        }
    }

    pub enum LeftMaybeAscend {}
    impl NodeAction for LeftMaybeAscend {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf>> {
            cursor.left_maybe_ascend()
        }
    }

    pub enum RightMaybeAscend {}
    impl NodeAction for RightMaybeAscend {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf>> {
            cursor.right_maybe_ascend()
        }
    }

    pub enum DescendFirst {}
    impl NodeAction for DescendFirst {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf>> {
            cursor.descend_first()
        }
    }

    pub enum DescendLast {}
    impl NodeAction for DescendLast {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf>> {
            cursor.descend_last()
        }
    }

    pub enum NextLeaf {}
    impl LeafAction for NextLeaf {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&C::Leaf> {
            cursor.next_leaf()
        }
    }

    pub enum PrevLeaf {}
    impl LeafAction for PrevLeaf {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&C::Leaf> {
            cursor.prev_leaf()
        }
    }

    pub enum FirstLeaf {}
    impl LeafAction for FirstLeaf {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&C::Leaf> {
            cursor.first_leaf()
        }
    }

    pub enum LastLeaf {}
    impl LeafAction for LastLeaf {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&C::Leaf> {
            cursor.last_leaf()
        }
    }

    #[doc(hidden)]
    pub trait JumpActionSet {
        type AscendToTrue: NodeAction;
        type AscendToFalse: NodeAction;
        type TrueRootToLeaf: LeafAction;
        type SiblingToFalse: NodeAction;
        type DescendToFalse: NodeAction;
        type FalseLeafToTrue: LeafAction;
    }

    #[doc(hidden)]
    pub enum PrefixMin {}
    impl JumpActionSet for PrefixMin {
        type AscendToTrue = RightMaybeAscend;
        type AscendToFalse = LeftMaybeAscend;
        type TrueRootToLeaf = FirstLeaf;
        type SiblingToFalse = LeftSibling;
        type DescendToFalse = DescendLast;
        type FalseLeafToTrue = NextLeaf;
    }

    #[doc(hidden)]
    pub enum SuffixMax {}
    impl JumpActionSet for SuffixMax {
        type AscendToTrue = LeftMaybeAscend;
        type AscendToFalse = RightMaybeAscend;
        type TrueRootToLeaf = LastLeaf;
        type SiblingToFalse = RightSibling;
        type DescendToFalse = DescendFirst;
        type FalseLeafToTrue = PrevLeaf;
    }
}
