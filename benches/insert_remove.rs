#![feature(test)]

// A set of totally unscientific and unfair benchmarks!

extern crate test;
extern crate infotree;

use infotree::{Leaf, InfoTree};
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
fn insert_remove_bts(b: &mut Bencher) {
    let mut tree = (0..TOTAL).collect::<BTreeSet<_>>();
    b.iter(|| {
        tree.remove(&0);
        tree.insert(0);
    })
}

#[bench]
fn insert_remove_ll(b: &mut Bencher) {
    let mut ll = (0..TOTAL).collect::<LinkedList<_>>();
    b.iter(|| {
        ll.pop_front();
        ll.push_front(0);
    })
}

#[bench]
fn insert_remove_it(b: &mut Bencher) {
    let mut tree = (0..TOTAL).map(|e| TestLeaf(e)).collect::<InfoTree<_>>();
    b.iter(|| {
        tree.pop_front();
        tree.push_front(TestLeaf(0));
    })
}

#[bench]
fn insert_remove_vec(b: &mut Bencher) {
    let mut vec = (0..TOTAL).collect::<Vec<_>>();
    b.iter(|| {
        vec.remove(0);
        vec.insert(0, 0);
    })
}
