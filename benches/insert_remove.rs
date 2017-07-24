#![feature(test)]

extern crate test;
extern crate infotree;

use infotree::traits::Leaf;

use test::Bencher;

use std::collections::BTreeSet;

const TOTAL: usize = 8192;

#[derive(Clone)]
struct TestLeaf(usize);

impl Leaf for TestLeaf {
    type Info = ();
    fn compute_info(&self) { }
}

#[bench]
fn btreeset_insert_remove(b: &mut Bencher) {
    let mut tree = (1..TOTAL).collect::<BTreeSet<_>>();
    b.iter(|| {
        tree.insert(0);
        tree.remove(&0)
    })
}
