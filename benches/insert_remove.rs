#![feature(test)]

// A set of totally unscientific and unfair benchmarks!

extern crate test;
extern crate infotree;

use infotree::{CursorMut, Leaf};
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
fn btreeset_insert_remove(b: &mut Bencher) {
    let mut tree = (1..TOTAL).collect::<BTreeSet<_>>();
    b.iter(|| {
        tree.insert(0);
        tree.remove(&0);
    })
}

#[bench]
fn linkedlist_push_pop(b: &mut Bencher) {
    let mut ll = (1..TOTAL).collect::<LinkedList<_>>();
    b.iter(|| {
        ll.push_front(0);
        ll.pop_front();
    })
}

#[bench]
fn cursormut_insert_remove(b: &mut Bencher) {
    let mut cm = (1..TOTAL).map(|e| TestLeaf(e)).collect::<CursorMut<_, ()>>();
    cm.reset();
    b.iter(|| {
        cm.insert_first(TestLeaf(0));
        cm.remove_first();
    })
}

#[bench]
fn vec_insert_remove(b: &mut Bencher) {
    let mut vec = (1..TOTAL).collect::<Vec<_>>();
    b.iter(|| {
        vec.insert(0, 0);
        vec.remove(0);
    })
}
