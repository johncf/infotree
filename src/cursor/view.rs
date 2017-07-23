use super::conf::{CConf, Rc33M};
use super::nav::CursorNav;
use node::Node;
use traits::{Leaf, PathInfo, SubOrd};
use mines::SliceExt; // for boom_get

use arrayvec::ArrayVec;

use std::fmt;

/// An object that can be used to traverse a `Node`.
///
/// `Cursor` is very lightweight. All operations are done entirely using stack memory -- no
/// heap allocations are made at any point.
///
/// Note: `Cursor` takes more than 200B on stack (exact size mainly depends on the size of `PI`)
pub struct Cursor<'a, L, PI, CONF = Rc33M>
    where L: Leaf + 'a,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    root: &'a Node<L, CONF::Ptr>,
    steps: ArrayVec<CONF::StepsBuf>,
}

pub struct CStep<'a, L, PI, CONF>
    where L: Leaf + 'a,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    nodes: &'a [Node<L, CONF::Ptr>],
    idx: usize, // index at which cursor descended
    path_info: PI,
}

impl<'a, L, PI, CONF> Clone for Cursor<'a, L, PI, CONF>
    where L: Leaf + Clone + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    fn clone(&self) -> Self {
        Cursor {
            root: self.root,
            steps: self.steps.clone(),
        }
    }
}

impl<'a, L, PI, CONF> Clone for CStep<'a, L, PI, CONF>
    where L: Leaf + Clone + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    fn clone(&self) -> Self {
        CStep {
            nodes: self.nodes,
            idx: self.idx,
            path_info: self.path_info.clone(),
        }
    }
}

impl<'a, L, PI, CONF> fmt::Debug for CStep<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: fmt::Debug,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CStep {{ nodes.len: {}, idx: {}, path_info: {:?} }}",
                  self.nodes.len(), self.idx, self.path_info)
    }
}

impl<'a, L, PI, CONF> fmt::Debug for Cursor<'a, L, PI, CONF>
    where L: Leaf + 'a,
          L::Info: fmt::Debug,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    /// Prints the tree under the current node.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut cursor = Self::new(self.current());
        let mut height = cursor.height();
        loop {
            while cursor.height() > height {
                let _res = cursor.descend_first();
                debug_assert!(_res.is_some());
            }
            write!(f, "{}: ", height)?;
            loop {
                write!(f, "{:?} ", cursor.current().children().len())?;
                if cursor.right_sibling().is_none() {
                    if cursor.next_node().is_some() {
                        write!(f, "// ")?;
                    } else {
                        break;
                    }
                }
            }
            if height == 0 { break; }
            else {
                writeln!(f)?;
                height -= 1;
            }
            cursor.reset();
        }
        Ok(())
    }
}

impl<'a, L, PI, CONF> Cursor<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    /// Create a new cursor from a root node.
    pub fn new(node: &'a Node<L, CONF::Ptr>) -> Self {
        Cursor {
            root: node,
            steps: ArrayVec::new(),
        }
    }

    /// Returns a reference to the root node.
    pub fn root(&self) -> &'a Node<L, CONF::Ptr> {
        self.root
    }

    /// Returns a reference to the current node, where the cursor is at.
    pub fn current(&self) -> &'a Node<L, CONF::Ptr> {
        match self.steps.last() {
            Some(cstep) => unsafe { &cstep.nodes.boom_get(cstep.idx) },
            None => self.root,
        }
    }

    /// Returns a reference to the leaf's value if the current node is a leaf.
    pub fn leaf(&self) -> Option<&'a L> {
        self.current().leaf()
    }

    /// Height of the current node from leaves.
    pub fn height(&self) -> usize {
        self.current().height()
    }

    /// Returns whether the cursor is currently at the root of the tree.
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

    /// See [`CursorMut::descend_by`] for more details.
    ///
    /// [`CursorMut::descend_by`]: struct.CursorMut.html#method.descend_by
    pub fn descend_by<F>(&mut self, f: F, reversed: bool) -> Option<&'a Node<L, CONF::Ptr>>
        where F: FnMut(PI, L::Info, usize, usize) -> bool
    {
        let cur_node = self.current();
        let res = if reversed {
            cur_node.path_traverse_rev(self.path_info(), f)
        } else {
            cur_node.path_traverse(self.path_info(), f)
        };
        match res {
            Ok((index, path_info, child)) => {
                self.descend_raw(cur_node.children(), index, path_info);
                Some(child)
            }
            Err(_) => None,
        }
    }

    fn descend_raw(&mut self, nodes: &'a [Node<L, CONF::Ptr>], idx: usize, path_info: PI) {
        // ArrayVec::push(e) returns Some(e) on overflow!
        assert!(self.steps.push(CStep { nodes, idx, path_info }).is_none());
    }

    pub fn reset(&mut self) {
        self.steps.clear();
    }

    pub fn ascend(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        self.steps.pop().map(|cstep| &cstep.nodes[cstep.idx])
    }

    pub fn descend_first(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        self.descend_by(|_, _, _, _| true, false)
    }

    pub fn descend_last(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        self.descend_by(|_, _, _, _| true, true)
    }

    pub fn left_sibling(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        let &mut Cursor { ref root, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CStep { nodes, ref mut idx, ref mut path_info }) => {
                if *idx > 0 {
                    *idx -= 1;
                    *path_info = path_info.extend_inv(nodes[*idx].info());
                    Some(root)
                } else {
                    None
                }
            }
            None => None, // at the root
        }
    }

    pub fn right_sibling(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        let &mut Cursor { ref root, ref mut steps } = self;
        match steps.last_mut() {
            Some(&mut CStep { nodes, ref mut idx, ref mut path_info }) => {
                if *idx + 1 < nodes.len() {
                    *path_info = path_info.extend(nodes[*idx].info());
                    *idx += 1;
                    Some(root)
                } else {
                    None
                }
            }
            None => None, // at the root
        }
    }

    pub fn first_leaf(&mut self) -> Option<&'a L> {
        let short_lived: Option<&L> = <Self as CursorNav>::first_leaf(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    pub fn last_leaf(&mut self) -> Option<&'a L> {
        let short_lived: Option<&L> = <Self as CursorNav>::last_leaf(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    pub fn next_node(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        let short_lived: Option<&Node<_, _>> = <Self as CursorNav>::next_node(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    pub fn prev_node(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        let short_lived: Option<&Node<_, _>> = <Self as CursorNav>::prev_node(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    pub fn next_leaf(&mut self) -> Option<&'a L> {
        let short_lived: Option<&L> = <Self as CursorNav>::next_leaf(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    pub fn prev_leaf(&mut self) -> Option<&'a L> {
        let short_lived: Option<&L> = <Self as CursorNav>::prev_leaf(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    pub fn left_maybe_ascend(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        let short_lived: Option<&Node<_, _>> = <Self as CursorNav>::left_maybe_ascend(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    pub fn right_maybe_ascend(&mut self) -> Option<&'a Node<L, CONF::Ptr>> {
        let short_lived: Option<&Node<_, _>> = <Self as CursorNav>::right_maybe_ascend(self);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    /// See [`CursorMut::find_min`] for more details.
    ///
    /// [`CursorMut::find_min`]: struct.CursorMut.html#method.find_min
    pub fn find_min<IS>(&mut self, info_sub: IS) -> Option<&'a L>
        where IS: SubOrd<L::Info>,
    {
        let short_lived: Option<&L> = <Self as CursorNav>::find_min(self, info_sub);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    /// See [`CursorMut::find_max`] for more details.
    ///
    /// [`CursorMut::find_max`]: struct.CursorMut.html#method.find_max
    pub fn find_max<IS>(&mut self, info_sub: IS) -> Option<&'a L>
        where IS: SubOrd<L::Info>,
    {
        let short_lived: Option<&L> = <Self as CursorNav>::find_max(self, info_sub);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    /// See [`CursorMut::goto_min`] for more details.
    ///
    /// [`CursorMut::goto_min`]: struct.CursorMut.html#method.goto_min
    pub fn goto_min<PS: SubOrd<PI>>(&mut self, path_info_sub: PS) -> Option<&'a L> {
        let short_lived: Option<&L> = <Self as CursorNav>::goto_min(self, path_info_sub);
        unsafe { ::std::mem::transmute(short_lived) }
    }

    /// See [`CursorMut::goto_max`] for more details.
    ///
    /// [`CursorMut::goto_max`]: struct.CursorMut.html#method.goto_max
    pub fn goto_max<PS: SubOrd<PI>>(&mut self, path_info_sub: PS) -> Option<&'a L> {
        let short_lived: Option<&L> = <Self as CursorNav>::goto_max(self, path_info_sub);
        unsafe { ::std::mem::transmute(short_lived) }
    }
}

impl<'a, L, PI, CONF> CursorNav for Cursor<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
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

    fn _leaf(&self) -> Option<&L> {
        self.leaf()
    }

    fn _height(&self) -> Option<usize> {
        Some(self.height())
    }

    fn _current(&self) -> Option<&Node<L, CONF::Ptr>> {
        Some(self.current())
    }

    fn _current_must(&self) -> &Node<L, CONF::Ptr> {
        self.current()
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

impl<'a, L, PI, CONF> IntoIterator for Cursor<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    type IntoIter = LeafIter<'a, L, PI, CONF>;
    type Item = &'a L;

    fn into_iter(mut self) -> Self::IntoIter {
        self.reset();
        LeafIter {
            inner: self,
            init_done: false,
        }
    }
}

pub struct LeafIter<'a, L, PI, CONF>
    where L: Leaf + 'a,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    inner: Cursor<'a, L, PI, CONF>,
    init_done: bool,
}

impl<'a, L, PI, CONF> Iterator for LeafIter<'a, L, PI, CONF>
    where L: Leaf + 'a,
          PI: PathInfo<L::Info>,
          CONF: CConf<'a, L, PI>,
          CONF::Ptr: 'a,
{
    type Item = &'a L;
    fn next(&mut self) -> Option<&'a L> {
        if !self.init_done {
            self.init_done = true;
            self.inner.first_leaf()
        } else {
            self.inner.next_leaf()
        }
    }
}

#[cfg(test)]
mod tests {
    use cursor::Cursor;
    use test_help::*;

    #[test]
    fn leaf_traversal() {
        let tree: NodeRc<_> = (1..21).map(|i| ListLeaf(i)).collect();
        let mut leaf_iter = CursorT::new(&tree).into_iter();
        for i in 1..21 {
            assert_eq!(leaf_iter.next(), Some(&ListLeaf(i)));
        }
        assert_eq!(leaf_iter.next(), None);
        let mut cursor = CursorT::new(&tree);
        assert_eq!(cursor.last_leaf(), Some(&ListLeaf(20)));
        for i in (1..20).rev() {
            assert_eq!(cursor.prev_leaf(), Some(&ListLeaf(i)));
        }
        assert_eq!(cursor.prev_leaf(), None);
    }

    #[test]
    fn path_extend() {
        let tree: NodeRc<_> = (1..21).map(|i| ListLeaf(i)).collect();
        let mut cursor = Cursor::<_, ListPath>::new(&tree);
        assert_eq!(cursor.first_leaf().unwrap(), &ListLeaf(1));
        assert_eq!(cursor.path_info(), ListPath { index: 0, run: 0 });
        cursor.reset();
        assert_eq!(cursor.last_leaf().unwrap(), &ListLeaf(20));
        assert_eq!(cursor.path_info(), ListPath { index: 19, run: 19*20/2 });
    }

    // FIXME need more tests
}
