#![feature(test)]

// A set of totally unscientific and unfair benchmarks!

extern crate test;
extern crate infotree;

use infotree::{Node, Leaf, CursorMut};
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
fn btreeset_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<BTreeSet<_>>();
    })
}

#[bench]
fn linkedlist_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<LinkedList<_>>();
    })
}

#[bench]
fn cursormut_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMut<_, ()>>();
    })
}

#[bench]
fn cursormut_insert(b: &mut Bencher) {
    b.iter(|| {
        let mut cursor_mut: CursorMut<_, ()> = CursorMut::new();
        for i in 0..TOTAL {
            cursor_mut.insert_last(TestLeaf(i));
        }
    })
}

#[bench]
fn node_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<Node<_>>();
    })
}

#[bench]
fn node_concat(b: &mut Bencher) {
    b.iter(|| {
        let mut node = Node::from_leaf(TestLeaf(0));
        for i in 1..TOTAL {
            node = Node::concat(node, Node::from_leaf(TestLeaf(i)));
        }
    })
}

#[bench]
fn vec_collect(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<Vec<_>>();
    })
}
