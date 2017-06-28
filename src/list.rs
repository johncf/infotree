use cursor::{Cursor, CursorMut};
use cursor::conf::{CConf, CMutConf, Rc33M};
use node::Node;
use traits::Leaf;

use std::collections::Bound;

#[doc(hidden)]
#[derive(Clone)]
pub struct ListLeaf<T: Clone>(T);

type ListInfo = usize;
type ListIndex = usize;

impl<T: Clone> Leaf for ListLeaf<T> {
    type Info = ListInfo;
    fn compute_info(&self) -> ListInfo { 1 }
}

#[derive(Clone)]
pub struct List<T, CONF=Rc33M>
    where T: Clone, CONF: CMutConf<ListLeaf<T>, ListIndex>,
{
    inner: CursorMut<ListLeaf<T>, ListIndex, CONF>,
    len_cache: usize,
}

#[derive(Clone)]
pub struct ListView<'a, T, CONF>
    where T: Clone + 'a,
          CONF: CConf<'a, ListLeaf<T>, ListIndex>,
          CONF::Ptr: 'a,
{
    inner: Cursor<'a, ListLeaf<T>, ListIndex, CONF>,
    len_cache: usize,
}

impl<T, CONF> List<T, CONF>
    where T: Clone, CONF: CMutConf<ListLeaf<T>, ListIndex>,
{
    pub fn new() -> List<T> {
        List {
            inner: CursorMut::new(),
            len_cache: 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        debug_assert_eq!(self.inner.is_empty(), self.len_cache == 0);
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        //self.inner.reset();
        //self.inner.path_info()
        self.len_cache
    }

    pub fn insert(&mut self, _index: usize, _element: T) -> Result<(), T> {
        unimplemented!()
    }

    pub fn remove(&mut self, _index: usize) -> Result<T, ()> {
        unimplemented!()
    }

    pub fn push(&mut self, element: T) {
        self.inner.reset();
        self.inner.insert_leaf(ListLeaf(element), true);
        self.len_cache += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len_cache > 0 {
            self.len_cache -= 1;
            self.inner.reset();
            self.inner.last_leaf();
            Some(self.inner.remove_leaf().unwrap().0)
        } else {
            None
        }
    }

    pub fn append(&mut self, _other: &mut List<T>) {
        unimplemented!()
    }

    pub fn clear(&mut self) {
        self.inner = CursorMut::new();
    }

    pub fn get(&mut self, _index: usize) -> Option<&T> {
        unimplemented!()
    }

    pub fn first(&mut self) -> Option<&T> {
        unimplemented!()
    }

    pub fn last(&mut self) -> Option<&T> {
        unimplemented!()
    }

    pub fn split_off(&mut self, _index: usize) -> List<T> {
        unimplemented!()
    }
}

impl<'a, T, CONF> List<T, CONF>
    where T: Clone + 'a,
          CONF: CMutConf<ListLeaf<T>, ListIndex> + CConf<'a, ListLeaf<T>, ListIndex>,
          CONF::Ptr: 'a,
{
    /// Returns `None` if empty.
    pub fn view(&'a mut self) -> Option<ListView<'a, T, CONF>> {
        self.inner.reset();
        self.inner.current().map(|node| ListView::from_node(node))
    }
}

impl<T, CONF> Extend<T> for List<T, CONF>
    where T: Clone, CONF: CMutConf<ListLeaf<T>, ListIndex>,
{
    fn extend<I>(&mut self, _iter: I)
        where I: IntoIterator<Item=T>
    {
        unimplemented!()
    }
}

// ListView ---------------------------------------------------------------

impl<'a, T, CONF> ListView<'a, T, CONF>
    where T: Clone + 'a,
          CONF: CConf<'a, ListLeaf<T>, ListIndex>,
          CONF::Ptr: 'a,
{
    fn from_node(node: &'a Node<ListLeaf<T>, CONF::Ptr>) -> Self {
        ListView {
            inner: Cursor::new(node),
            len_cache: node.info(),
        }
    }

    pub fn len(&self) -> usize {
        self.len_cache
    }

    pub fn get(&self, _index: usize) -> Option<&T> {
        unimplemented!()
    }

    pub fn first(&self) -> Option<&T> {
        unimplemented!()
    }

    pub fn last(&self) -> Option<&T> {
        unimplemented!()
    }

    pub fn range(&self, start: Bound<usize>, end: Bound<usize>) -> Iter<'a, T, CONF> {
        let start = match start {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i.checked_add(1).unwrap(),
            Bound::Unbounded => 0,
        };
        let end = match end {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i.checked_sub(1).unwrap(),
            Bound::Unbounded => self.len_cache,
        };
        Iter {
            inner: Cursor::new(self.inner.root()),
            start: start,
            end: end,
        }
    }
}

pub struct Iter<'a, T, CONF>
    where T: Clone + 'a,
          CONF: CConf<'a, ListLeaf<T>, ListIndex>,
          CONF::Ptr: 'a,
{
    inner: Cursor<'a, ListLeaf<T>, ListIndex, CONF>,
    start: usize,
    end: usize,
}

impl<'a, T, CONF> Iterator for Iter<'a, T, CONF>
    where T: Clone + 'a, CONF: CConf<'a, ListLeaf<T>, ListIndex>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.start < self.end {
            unimplemented!()
        } else {
            None
        }
    }
}

impl<'a, T, CONF> DoubleEndedIterator for Iter<'a, T, CONF>
    where T: Clone + 'a, CONF: CConf<'a, ListLeaf<T>, ListIndex>,
{
    fn next_back(&mut self) -> Option<&'a T> {
        if self.start < self.end {
            unimplemented!()
        } else {
            None
        }
    }
}
