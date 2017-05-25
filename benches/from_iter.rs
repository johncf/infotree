#![feature(test)]

extern crate test;
extern crate unitree;

use unitree::{Leaf, UniTree};
use test::Bencher;

use std::collections::LinkedList;

const TOTAL: usize = 40960;

#[derive(Clone)]
struct TestLeaf(usize);

impl Leaf for TestLeaf {
    type Info = ();
    fn compute_info(&self) { }
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
        (0..TOTAL).map(|e| TestLeaf(e)).collect::<UniTree<_>>();
    })
}

#[bench]
fn from_iter_vec(b: &mut Bencher) {
    b.iter(|| {
        (0..TOTAL).collect::<Vec<_>>();
    })
}
