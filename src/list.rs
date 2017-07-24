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

pub struct List<T, CONF=Rc33M>
    where T: Clone, CONF: CMutConf<ListLeaf<T>, ListIndex>,
{
    inner: CursorMut<ListLeaf<T>, ListIndex, CONF>,
    len_cache: usize,
}

pub struct ListView<'a, T, CONF>
    where T: Clone + 'a,
          CONF: CConf<'a, ListLeaf<T>, ListIndex>,
          CONF::Ptr: 'a,
{
    inner: Cursor<'a, ListLeaf<T>, ListIndex, CONF>,
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

    pub fn len(&mut self) -> usize {
        self.inner.reset();
        self.inner.current().map(|n| n.info()).unwrap_or(0)
        //self.len_cache
    }

    pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
        let len = self.len();
        if index == len {
            self.push(element);
        } else if index < len {
            self.inner.goto_min(index);
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
        let len = self.len();
        if len > 0 {
            self.len_cache -= 1;
            {
                let leaf = self.inner.goto_max(len);
                debug_assert!(leaf.is_some());
            }
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

    pub fn get(&mut self, index: usize) -> Option<&T> {
        self.inner.goto_min(index).map(|l| &l.0)
    }

    pub fn first(&mut self) -> Option<&T> {
        self.inner.goto_min(0).map(|l| &l.0)
    }

    pub fn last(&mut self) -> Option<&T> {
        self.inner.goto_max(self.len_cache).map(|l| &l.0)
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

impl<T, CONF> Clone for List<T, CONF>
    where T: Clone, CONF: CMutConf<ListLeaf<T>, ListIndex>,
{
    fn clone(&self) -> Self {
        List {
            inner: self.inner.clone(),
            len_cache: self.len_cache,
        }
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
        }
    }

    pub fn len(&self) -> usize {
        self.inner.root().info()
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
        let len = self.len();
        &self.inner.goto_max(len).unwrap().0
    }

    pub fn iter(&self) -> Iter<'a, T, CONF> {
        self.range(Bound::Unbounded, Bound::Unbounded)
    }

    pub fn range(&self, start: Bound<usize>, end: Bound<usize>) -> Iter<'a, T, CONF> {
        let start = match start {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i.checked_add(1).unwrap(),
            Bound::Unbounded => 0,
        };
        let len = self.len();
        let end = match end {
            Bound::Included(i) if i < len => i.checked_add(1).unwrap(),
            Bound::Excluded(i) if i <= len => i,
            _ => len,
        };
        Iter {
            inner: Cursor::new(self.inner.root()),
            start: start,
            end: end,
        }
    }
}

impl<'a, T, CONF> Clone for ListView<'a, T, CONF>
    where T: Clone + 'a,
          CONF: CConf<'a, ListLeaf<T>, ListIndex>,
          CONF::Ptr: 'a,
{
    fn clone(&self) -> Self {
        ListView {
            inner: self.inner.clone(),
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
            let ret = self.inner.goto_min(self.start).unwrap();
            self.start += 1;
            Some(&ret.0)
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
            let ret = self.inner.goto_max(self.end).unwrap();
            self.end -= 1;
            Some(&ret.0)
        } else {
            None
        }
    }
}

impl<'a, T, CONF> Clone for Iter<'a, T, CONF>
    where T: Clone + 'a, CONF: CConf<'a, ListLeaf<T>, ListIndex>,
{
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
            start: self.start,
            end: self.end,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::List;

    #[test]
    fn from_iter() {
        let mut list: List<_> = (0..256).collect();
        for i in 0..256 {
            assert_eq!(list.get(i), Some(&i));
        }
    }

    #[test]
    fn view_iter() {
        let mut list: List<_> = (0..256).collect();
        let view = list.view().unwrap();
        let mut iter = view.iter();
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next_back(), Some(&255));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next_back(), Some(&254));
        assert_eq!(iter.next_back(), Some(&253));
        assert_eq!(iter.next(), Some(&2));
        let mut iter = view.iter();
        for i in 0..256 {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);
        let mut iter = view.iter();
        for i in (0..256).rev() {
            assert_eq!(iter.next_back(), Some(&i));
        }
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn push_pop() {
        let mut list: List<_> = (0..242).collect();
        for i in 242..256 {
            list.push(i);
        }
        for (i, j) in list.view().unwrap().iter().enumerate() {
            assert_eq!(i, *j);
        }
        for i in (0..256).rev() {
            assert_eq!(list.len(), i + 1);
            assert_eq!(list.pop(), Some(i));
        }
    }
}
