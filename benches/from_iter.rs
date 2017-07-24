#![feature(test)]

// A set of totally unscientific and unfair benchmarks!

extern crate test;
extern crate infotree;
extern crate im;

use infotree::cursor::CursorMut;
use infotree::cursor::conf::{Arc33M, Rc33M, Box33M};
use infotree::node::{Node, Arc16, Rc16, Box16};
use infotree::traits::Leaf;
use infotree::list::List;

use im::list::List as ImList;
use im::conslist::ConsList;

type NodeBox<L> = Node<L, Box16<L>>;

type CursorMutArc<L> = CursorMut<L, (), Arc33M>;
type CursorMutRc<L> = CursorMut<L, (), Rc33M>;
type CursorMutBox<L> = CursorMut<L, (), Box33M>;

type ListArc<T> = List<T, Arc33M>;

use test::Bencher;

use std::collections::LinkedList;
use std::collections::BTreeSet;

const TOTAL: usize = 4096;

#[derive(Clone)]
struct TestLeaf(usize);

impl Leaf for TestLeaf {
    type Info = ();
    fn compute_info(&self) { }
}

#[bench]
fn a00_vec_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<Vec<_>>()
    })
}

#[bench]
fn a01_linkedlist_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<LinkedList<_>>()
    })
}

#[bench]
fn a02_btreeset_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<BTreeSet<_>>()
    })
}

// Note that CursorMut::from_iter collects 16 elements at once from the iterator to construct a
// node of leafs at once. So, of course, it would be faster than both BTreeSet and LinkedList.

#[bench]
fn cursormut_collect_arc(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMutArc<_>>()
    })
}

#[bench]
fn cursormut_collect_rc(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMutRc<_>>()
    })
}

#[bench]
fn cursormut_collect_box(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMutBox<_>>()
    })
}

#[bench]
fn cursormut_insert_arc(b: &mut Bencher) {
    b.iter(|| {
        let mut cursor_mut = CursorMutArc::new();
        for i in 0..TOTAL {
            cursor_mut.insert_leaf(TestLeaf(i), true);
        }
        cursor_mut
    })
}

#[bench]
fn cursormut_insert_rc(b: &mut Bencher) {
    b.iter(|| {
        let mut cursor_mut = CursorMutRc::new();
        for i in 0..TOTAL {
            cursor_mut.insert_leaf(TestLeaf(i), true);
        }
        cursor_mut
    })
}

#[bench]
fn cursormut_insert_box(b: &mut Bencher) {
    b.iter(|| {
        let mut cursor_mut = CursorMutBox::new();
        for i in 0..TOTAL {
            cursor_mut.insert_leaf(TestLeaf(i), true);
        }
        cursor_mut
    })
}

#[bench]
fn list_insert_arc(b: &mut Bencher) {
    b.iter(|| {
        let mut list = ListArc::new();
        for i in 0..TOTAL {
            list.push(i);
        }
        list
    })
}

#[bench]
fn list_insert_cloned_arc(b: &mut Bencher) {
    b.iter(|| {
        let mut list = ListArc::new();
        for i in 0..TOTAL {
            let mut list2 = list.clone();
            list2.push(i);
            list = list2;
        }
        list
    })
}

#[bench]
fn im_list_cons(b: &mut Bencher) {
    b.iter(|| {
        let mut l = ImList::new();
        for i in 0..TOTAL {
            l = l.cons(i)
        }
    })
}

#[bench]
fn im_conslist_cons(b: &mut Bencher) {
    b.iter(|| {
        let mut l = ConsList::new();
        for i in 0..TOTAL {
            l = l.cons(i)
        }
    })
}

#[bench]
fn node_collect_box(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<NodeBox<_>>()
    })
}

#[bench]
fn node_concat_box(b: &mut Bencher) {
    b.iter(|| {
        let mut node = NodeBox::from_leaf(TestLeaf(0));
        for i in 1..TOTAL {
            node = NodeBox::concat(node, NodeBox::from_leaf(TestLeaf(i)));
        }
        node
    })
}

#[bench]
fn node_concat_cursor_box(b: &mut Bencher) {
    b.iter(|| {
        let mut node = NodeBox::from_leaf(TestLeaf(0));
        for i in 1..TOTAL {
            node = NodeBox::concat_with_cursor::<Box33M>(node, NodeBox::from_leaf(TestLeaf(i)));
        }
        node
    })
}

#[bench]
fn node_concat_steps_box(b: &mut Bencher) {
    b.iter(|| {
        let mut node = NodeBox::from_leaf(TestLeaf(0));
        for i in 1..TOTAL {
            node = NodeBox::concat_with_steps::<Box33M>(node, NodeBox::from_leaf(TestLeaf(i)));
        }
        node
    })
}
