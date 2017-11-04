#![feature(test)]

extern crate test;
extern crate infotree;

use infotree::test_help::{NodeRc, ListLeaf, ListPath, ListIndex};

use test::Bencher;

use std::collections::BTreeSet;

const TOTAL: usize = 8192;

#[bench]
fn btreeset_insert_remove(b: &mut Bencher) {
    let mut tree = (1..TOTAL).collect::<BTreeSet<_>>();
    b.iter(|| {
        tree.insert(0);
        tree.remove(&0)
    })
}

#[bench]
fn node_clone_remove(b: &mut Bencher) {
    use infotree::node::PathRange;
    let total = 1028;
    let cut_from = 273;
    let cut_to = 700;
    let node: NodeRc<_> = (0..total).map(|i| ListLeaf(i)).collect();
    b.iter(|| {
        let node = node.clone();
        node.remove_subseq::<ListPath, _>(PathRange { left: ListIndex(cut_from), right: ListIndex(cut_to) })
    });
}
