#![feature(test)]

// A set of totally unscientific and unfair benchmarks!

extern crate test;
extern crate infotree;

use infotree::{Leaf, InfoTree, CursorMutT};
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
fn from_iter_bts(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<BTreeSet<_>>();
    })
}

#[bench]
fn from_iter_ll(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<LinkedList<_>>();
    })
}

#[bench]
fn from_iter_cm(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMutT<_>>();
    })
}

#[bench]
fn from_iter_cm_raw(b: &mut Bencher) {
    b.iter(|| {
        let mut cursor_mut = CursorMutT::new();
        for i in 0..TOTAL {
            cursor_mut.insert_after(TestLeaf(i));
        }
    })
}

#[bench]
fn from_iter_it(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<InfoTree<_>>();
    })
}

#[bench]
fn from_iter_vec(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<Vec<_>>();
    })
}
