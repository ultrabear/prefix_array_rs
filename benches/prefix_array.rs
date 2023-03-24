use criterion::{black_box, criterion_group, criterion_main, Criterion};
use prefix_array::PrefixArraySet;

fn bigvec() -> Vec<String> {
    const N: usize = 1 << 20;

    (0..N).map(|v| v.to_string()).collect()
}

pub fn benchy(c: &mut Criterion) {
    let big = bigvec();
    let big2 = big.clone();

    let arr = PrefixArraySet::from_vec_lossy(big);
    let trie = radix_trie::Trie::from_iter(big2.into_iter().map(|s| (s, ())));

    c.bench_function("find_with_prefix_2^20", |b| {
        b.iter(|| black_box(arr.find_all_with_prefix(black_box("6"))))
    });
    c.bench_function("find_with_prefix_2^20-trie", |b| {
        b.iter(|| black_box(trie.get_raw_descendant(black_box("6"))))
    });

    let arr2 = arr.find_all_with_prefix("6543").to_owned();
    let mut arr3 = PrefixArraySet::new();

    c.bench_function("clone_native", |b| b.iter(|| black_box(arr2.clone())));

    c.bench_function("clone_from", |b| b.iter(|| arr3.clone_from(&arr2)));
}

criterion_group!(benches, benchy);
criterion_main!(benches);
