#![feature(test)]

// A set of totally unscientific and unfair benchmarks!

extern crate test;
extern crate infotree;

use infotree::node::{Node, Arc16, Rc16, Box16};
use infotree::traits::Leaf;

type NodeArc<L> = Node<L, Arc16<L>>;
type NodeRc<L> = Node<L, Rc16<L>>;
type NodeBox<L> = Node<L, Box16<L>>;

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

#[bench]
fn node_collect_arc(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<NodeArc<_>>()
    })
}

#[bench]
fn node_collect_rc(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<NodeRc<_>>()
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
