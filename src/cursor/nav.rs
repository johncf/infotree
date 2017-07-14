use node::Node;
use traits::{Leaf, PathInfo, SubOrd};
use node::NodesPtr;
use self::actions::{NodeAction, LeafAction};

pub trait CursorNav: Sized {
    type Leaf: Leaf;
    type NodesPtr: NodesPtr<Self::Leaf>;
    type PathInfo: PathInfo<<Self::Leaf as Leaf>::Info>;

    fn _is_root(&self) -> bool;
    fn _path_info(&self) -> Self::PathInfo;
    fn _leaf(&self) -> Option<&Self::Leaf>;
    fn _height(&self) -> Option<usize>;
    fn _current(&self) -> Option<&Node<Self::Leaf, Self::NodesPtr>>;
    fn _current_must(&self) -> &Node<Self::Leaf, Self::NodesPtr>;

    fn _reset(&mut self);
    fn _ascend(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>>;
    fn _descend_first(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>>;
    fn _descend_last(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>>;
    fn _left_sibling(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>>;
    fn _right_sibling(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>>;

    fn first_leaf(&mut self) -> Option<&Self::Leaf> {
        while self._descend_first().is_some() {}
        self._leaf()
    }

    fn last_leaf(&mut self) -> Option<&Self::Leaf> {
        while self._descend_last().is_some() {}
        self._leaf()
    }

    fn next_node(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>> {
        let height = self._height();
        if self.right_maybe_ascend().is_some() {
            let height = height.unwrap();
            while self._current_must().height() > height {
                let _res = self._descend_first();
                debug_assert!(_res.is_some());
            }
            Some(&self._current_must())
        } else {
            None
        }
    }

    fn prev_node(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>> {
        let height = self._height();
        if self.left_maybe_ascend().is_some() {
            let height = height.unwrap();
            while self._current_must().height() > height {
                let _res = self._descend_last();
                debug_assert!(_res.is_some());
            }
            Some(self._current_must())
        } else {
            None
        }
    }

    fn next_leaf(&mut self) -> Option<&Self::Leaf> {
        self.next_node().and_then(|n| n.leaf())
    }

    fn prev_leaf(&mut self) -> Option<&Self::Leaf> {
        self.prev_node().and_then(|n| n.leaf())
    }

    fn left_maybe_ascend(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>> {
        loop {
            if self._left_sibling().is_some() {
                return Some(self._current_must());
            } else if self._ascend().is_none() {
                return None;
            }
        }
    }

    fn right_maybe_ascend(&mut self) -> Option<&Node<Self::Leaf, Self::NodesPtr>> {
        loop {
            if self._right_sibling().is_some() {
                return Some(self._current_must());
            } else if self._ascend().is_none() {
                return None;
            }
        }
    }

    fn action_till<A, F>(&mut self, predicate: F) -> bool
        where A: actions::NodeAction,
              F: Fn(Self::PathInfo, <Self::Leaf as Leaf>::Info) -> bool
    {
        while A::act_on(self).is_some() {
            if predicate(self._path_info(), self._current_must().info()) {
                return true;
            }
        }
        return false;
    }

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
        match self._current().map(|n| satisfies(self._path_info(), n.info())) {
            Some(true) => {
                if !self.action_till::<JAS::AscendToFalse, _>(|path_info, info| !satisfies(path_info, info)) {
                    // condition is satisfied at root
                    return JAS::TrueRootToLeaf::act_on(self); // must unwrap
                }
                status = FindStatus::HitTrue;
            },
            Some(false) => {
                if self._is_root() {
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

        debug_assert!(!satisfies(self._path_info(), self._current().unwrap().info()));

        // descend till the last leaf that don't satisfy the condition
        while self.action_till::<JAS::DescendToFalse, _>(|path_info, info| satisfies(path_info, info)) {
            status = FindStatus::HitTrue;
            if !self.action_till::<JAS::SiblingToFalse, _>(|path_info, info| !satisfies(path_info, info)) {
                // there must be a sibling that don't satisfy the condition
                unreachable!();
            }
        }

        debug_assert!(self._leaf().is_some());
        debug_assert!(!satisfies(self._path_info(), self._current().unwrap().info()));

        match status {
            FindStatus::HitRoot => None,
            FindStatus::HitTrue => JAS::FalseLeafToTrue::act_on(self), // must unwrap
        }
    }

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
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf, C::NodesPtr>>;
    }

    pub trait LeafAction {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&C::Leaf>;
    }

    pub enum LeftSibling {}
    impl NodeAction for LeftSibling {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf, C::NodesPtr>> {
            cursor._left_sibling()
        }
    }

    pub enum RightSibling {}
    impl NodeAction for RightSibling {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf, C::NodesPtr>> {
            cursor._right_sibling()
        }
    }

    pub enum LeftMaybeAscend {}
    impl NodeAction for LeftMaybeAscend {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf, C::NodesPtr>> {
            cursor.left_maybe_ascend()
        }
    }

    pub enum RightMaybeAscend {}
    impl NodeAction for RightMaybeAscend {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf, C::NodesPtr>> {
            cursor.right_maybe_ascend()
        }
    }

    pub enum DescendFirst {}
    impl NodeAction for DescendFirst {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf, C::NodesPtr>> {
            cursor._descend_first()
        }
    }

    pub enum DescendLast {}
    impl NodeAction for DescendLast {
        fn act_on<C: CursorNav>(cursor: &mut C) -> Option<&Node<C::Leaf, C::NodesPtr>> {
            cursor._descend_last()
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
