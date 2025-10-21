use criterion::{Criterion, criterion_group, criterion_main};

fn simple_bench(c: &mut Criterion) {
    println!("Starting simple benchmark");
    c.bench_function("simple", |b| b.iter(|| 2 + 2));
}

criterion_group!(benches, simple_bench);
criterion_main!(benches);
