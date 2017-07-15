use cursor::{Cursor, CursorMut};
use cursor::conf::{CConf, CMutConf, Rc33M};
use node::Node;
use traits::Leaf;

use std::collections::Bound;
use std::iter::FromIterator;

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

    pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
        let len = self.len();
        if index == len {
            self.push(element);
        } else if index < len {
            self.inner.goto_max(index);
            self.inner.insert_leaf(ListLeaf(element), false);
        } else {
            return Err(element);
        }
        self.len_cache += 1;
        Ok(())
    }

    pub fn remove(&mut self, _index: usize) -> Result<T, ()> {
        unimplemented!()
    }

    pub fn push(&mut self, element: T) {
        let len = self.len();
        self.inner.goto_max(len);
        self.inner.insert_leaf(ListLeaf(element), true);
        self.len_cache += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len_cache > 0 {
            let len = self.len();
            self.len_cache -= 1;
            self.inner.goto_max(len);
            Some(self.inner.remove_node().and_then(|n| n.into_leaf().ok()).unwrap().0)
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

    pub fn get(&mut self, index: usize) -> Option<&T> {
        if self.inner.goto_max(index).is_some() {
            let path = self.inner.path_info();
            if path == index {
                self.inner.leaf().map(|l| &l.0)
            } else {
                None
            }
        } else {
            None
        }
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

impl<T, CONF> FromIterator<T> for List<T, CONF>
    where T: Clone, CONF: CMutConf<ListLeaf<T>, ListIndex>,
{
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let iter = iter.into_iter().map(|e| ListLeaf(e));
        let mut inner: CursorMut<_, ListIndex, _> = iter.collect();
        inner.reset();
        let len_cache = inner.current().map(|n| n.info()).unwrap_or(0);
        List { inner, len_cache }
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

    pub fn get(&mut self, index: usize) -> Option<&T> {
        if index + 1 == self.len() {
            return Some(self.last())
        } else {
            if self.inner.goto_min(index).is_some() {
                let path = self.inner.path_info();
                if path == index {
                    return self.inner.leaf().map(|l| &l.0);
                }
            }
        }
        None
    }

    pub fn first(&mut self) -> &T {
        &self.inner.goto_min(0).unwrap().0
    }

    pub fn last(&mut self) -> &T {
        &self.inner.goto_max(self.len_cache).unwrap().0
    }

    pub fn range(&self, start: Bound<usize>, end: Bound<usize>) -> Iter<'a, T, CONF> {
        let start = match start {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i.checked_add(1).unwrap(),
            Bound::Unbounded => 0,
        };
        let end = match end {
            Bound::Included(i) => i.checked_add(1).unwrap(),
            Bound::Excluded(i) => i,
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
            if self.inner.goto_min(self.start).is_some() {
                let path = self.inner.path_info();
                if path == self.start {
                    self.start += 1;
                    return self.inner.leaf().map(|l| &l.0);
                }
            }
        }
        None
    }
}

impl<'a, T, CONF> DoubleEndedIterator for Iter<'a, T, CONF>
    where T: Clone + 'a, CONF: CConf<'a, ListLeaf<T>, ListIndex>,
{
    fn next_back(&mut self) -> Option<&'a T> {
        use traits::PathInfo;
        if self.start < self.end {
            if self.inner.goto_max(self.end).is_some() {
                let path = self.inner.path_info().extend(self.inner.current().info());
                if path == self.end {
                    self.end -= 1;
                    return self.inner.leaf().map(|l| &l.0);
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::{List, Bound};

    #[test]
    fn push() {
        let mut list: List<_> = (0..256).collect();
        list.push(256);
        assert_eq!(list.pop(), Some(256));
    }

    #[test]
    fn iter() {
        let mut list: List<_> = (0..256).collect();
        let mut iter = list.view().unwrap().range(Bound::Unbounded, Bound::Unbounded);
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next_back(), Some(&255));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next_back(), Some(&254));
        assert_eq!(iter.next_back(), Some(&253));
        assert_eq!(iter.next(), Some(&2));
    }
}
