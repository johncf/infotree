#![feature(test)]

// A set of totally unscientific and unfair benchmarks!

extern crate test;
extern crate infotree;

use infotree::{Leaf, InfoTree};
use test::Bencher;

use std::collections::LinkedList;
use std::collections::BTreeSet;

const TOTAL: usize = 40960;

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
fn from_iter_ut(b: &mut Bencher) {
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
