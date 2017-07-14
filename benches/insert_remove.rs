#![feature(test)]

extern crate test;
extern crate infotree;

use infotree::cursor;
use infotree::traits::Leaf;

type CursorMut<L> = cursor::CursorMut<L, ()>;

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

#[bench]
fn cm_insert_remove_local(b: &mut Bencher) {
    let mut cm = (1..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMut<_>>();
    cm.reset();
    cm.first_leaf();
    b.iter(|| {
        cm.insert_leaf(TestLeaf(0), false);
        cm.remove_leaf()
    })
}

#[bench]
fn cm_insert_remove_reset(b: &mut Bencher) {
    let mut cm = (1..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMut<_>>();
    b.iter(|| {
        cm.reset();
        cm.insert_leaf(TestLeaf(0), false);
        cm.remove_leaf()
    })
}

#[bench]
fn cm_insert_remove_local_cloned(b: &mut Bencher) {
    let mut cm = (1..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMut<_>>();
    cm.reset();
    cm.first_leaf();
    b.iter(|| {
        let mut cm = cm.clone();
        cm.insert_leaf(TestLeaf(0), false);
        cm.remove_leaf()
    })
}

#[bench]
fn cm_insert_remove_root_cloned(b: &mut Bencher) {
    let mut cm = (1..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMut<_>>();
    cm.reset();
    b.iter(|| {
        let mut cm = cm.clone();
        cm.insert_leaf(TestLeaf(0), false);
        cm.remove_leaf()
    })
}
