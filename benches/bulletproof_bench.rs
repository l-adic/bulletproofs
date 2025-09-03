use std::collections::HashMap;

use ark_secp256k1::{Fr, Projective};
use bulletproofs::{
    ipa::{
        BulletproofDomainSeparator, prove as ipa_prove,
        types::{CRS as IpaCRS, CrsSize, Witness as IpaWitness, statement},
        verify as ipa_verify,
    },
    range::{
        RangeProofDomainSeparator, prove as range_prove,
        types::{CRS as RangeCRS, Statement as RangeStatement, Witness as RangeWitness},
        verify as range_verify,
    },
};
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use rand::{RngCore, rngs::OsRng};
use spongefish::DomainSeparator;
use spongefish::codecs::arkworks_algebra::CommonGroupToUnit;

fn bench_ipa_prove_verify_cycle(c: &mut Criterion) {
    let mut group = c.benchmark_group("ipa");
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(80));

    // Test different CRS sizes (log values)
    let sizes = [2_u64, 4, 8, 16];

    let mut proofs: HashMap<u64, Vec<u8>> = HashMap::new();

    for size in sizes {
        let crs_size = CrsSize { log2_size: size };
        let crs: IpaCRS<Projective> = IpaCRS::rand(crs_size);

        // Create shared domain separator
        let domain_separator = DomainSeparator::new("ipa-benchmark");
        let domain_separator =
            BulletproofDomainSeparator::<Projective>::bulletproof_statement(domain_separator)
                .ratchet();
        let domain_separator =
            BulletproofDomainSeparator::<Projective>::add_bulletproof(domain_separator, crs.size());

        let witness = IpaWitness::rand(crs.size() as u64);
        let stmt = statement(&crs, &witness);

        // Benchmark prove
        group.bench_with_input(BenchmarkId::new("prove", size), &size, |b, _| {
            b.iter(|| {
                let mut prover_state = domain_separator.to_prover_state();
                prover_state.public_points(&[stmt.p]).unwrap();
                prover_state.ratchet().unwrap();

                let proof = ipa_prove(&mut prover_state, &crs, &stmt, &witness).unwrap();
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

                ipa_verify(verifier_state, &crs, &stmt).unwrap();
                black_box(())
            })
        });
    }

    group.finish();
}

fn bench_range_prove_verify_cycle<const N: usize>(c: &mut Criterion, crs: &RangeCRS<Projective>) {
    let mut group = c.benchmark_group(format!("range_{}", N));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(30));

    let mut rng = OsRng;

    let domain_separator = {
        let domain_separator = DomainSeparator::new("range-benchmark");
        let domain_separator =
            RangeProofDomainSeparator::<Projective>::range_proof_statement(domain_separator)
                .ratchet();
        RangeProofDomainSeparator::<Projective>::add_range_proof(domain_separator, N)
    };

    let mut proofs: HashMap<RangeStatement<N, Projective>, Vec<u8>> = HashMap::new();

    let max_val = (1u64 << N) - 1;
    let v = Fr::from(rng.next_u64() % max_val.max(1));
    let witness = RangeWitness::<N, Fr>::new(v, &mut rng);
    let statement = RangeStatement::<N, Projective>::new(crs, &witness);

    // Benchmark prove
    group.bench_with_input(BenchmarkId::new("prove", N), &N, |b, _| {
        b.iter(|| {
            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&[statement.v]).unwrap();
            prover_state.ratchet().unwrap();
            let proof =
                range_prove::<Projective, _, N>(prover_state, crs, &witness, &mut rng).unwrap();
            proofs.insert(statement, proof.clone());
            black_box(proof)
        })
    });

    // Benchmark verify using proof from HashMap
    group.bench_with_input(BenchmarkId::new("verify", N), &N, |b, _| {
        b.iter(|| {
            let proof = proofs.get(&statement).unwrap();
            let mut verifier_state = domain_separator.to_verifier_state(proof);
            verifier_state.public_points(&[statement.v]).unwrap();
            verifier_state.ratchet().unwrap();
            range_verify::<Projective, N>(verifier_state, crs, &statement).unwrap();
            black_box(())
        })
    });

    group.finish();
}

fn bench_range_proofs(c: &mut Criterion) {
    // Create shared CRS that's large enough for all range proof sizes we want to test
    let shared_crs = RangeCRS::rand(64);

    bench_range_prove_verify_cycle::<8>(c, &shared_crs);
    bench_range_prove_verify_cycle::<16>(c, &shared_crs);
    bench_range_prove_verify_cycle::<32>(c, &shared_crs);
    bench_range_prove_verify_cycle::<64>(c, &shared_crs);
}

criterion_group!(benches, bench_ipa_prove_verify_cycle, bench_range_proofs);
criterion_main!(benches);
