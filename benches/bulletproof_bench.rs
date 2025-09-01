use std::collections::HashMap;

use ark_secp256k1::Projective;
use bulletproofs::{
    ipa::{BulletproofDomainSeparator, prove, verify},
    types::{CRS, CrsSize, Witness, statement},
};
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use spongefish::DomainSeparator;
use spongefish::codecs::arkworks_algebra::CommonGroupToUnit;

fn bench_prove_verify_cycle(c: &mut Criterion) {
    let mut group = c.benchmark_group("bulletproof");
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(80));

    // Test different CRS sizes (log values)
    let sizes = [2 as u64, 4, 8, 16];

    let mut proofs: HashMap<u64, Vec<u8>> = HashMap::new();

    for size in sizes {
        let crs_size = CrsSize { log2_size: size };
        let crs: CRS<Projective> = CRS::rand(crs_size);

        // Create shared domain separator
        let domain_separator = DomainSeparator::new("benchmark");
        let domain_separator =
            BulletproofDomainSeparator::<Projective>::bulletproof_statement(domain_separator)
                .ratchet();
        let domain_separator =
            BulletproofDomainSeparator::<Projective>::add_bulletproof(domain_separator, crs.size());

        let witness = Witness::rand(crs.size() as u64);
        let stmt = statement(&crs, &witness);

        // Benchmark prove
        group.bench_with_input(BenchmarkId::new("prove", size), &size, |b, _| {
            b.iter(|| {
                let mut prover_state = domain_separator.to_prover_state();
                prover_state.public_points(&[stmt.p]).unwrap();
                prover_state.ratchet().unwrap();

                let proof = prove(prover_state, &crs, &stmt, &witness).unwrap();
                proofs.insert(size, proof.clone());
                black_box(proof)
            })
        });

        // Benchmark verify using the same domain separator and pre-generated proof
        group.bench_with_input(BenchmarkId::new("verify", size), &size, |b, _| {
            b.iter(|| {
                let proof = proofs.get(&size).unwrap();
                let mut verifier_state = domain_separator.to_verifier_state(proof);
                verifier_state.public_points(&[stmt.p]).unwrap();
                verifier_state.ratchet().unwrap();

                verify(verifier_state, &crs, &stmt).unwrap();
                black_box(())
            })
        });
    }

    group.finish();
}

criterion_group!(benches, bench_prove_verify_cycle);
criterion_main!(benches);
