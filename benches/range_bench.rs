mod common;

use ark_secp256k1::{Fr, Projective};
use bulletproofs::range::{
    RangeProofDomainSeparator, prove as range_prove,
    types::{CRS as RangeCRS, Statement as RangeStatement, Witness as RangeWitness},
    verify as range_verify,
};
use common::BoundedProofQueue;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rand::rngs::OsRng;
use spongefish::{DomainSeparator, codecs::arkworks_algebra::CommonGroupToUnit};

fn bench_range_prove_verify_cycle<Rng: rand::Rng>(
    c: &mut Criterion,
    crs: &RangeCRS<Projective>,
    n_bits: usize,
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group(format!("range_{}", n_bits));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(30));

    let domain_separator = {
        let domain_separator = DomainSeparator::new("range-benchmark");
        let domain_separator =
            RangeProofDomainSeparator::<Projective>::range_proof_statement(domain_separator)
                .ratchet();
        RangeProofDomainSeparator::<Projective>::add_range_proof(domain_separator, n_bits)
    };

    let mut proofs: BoundedProofQueue<(RangeStatement<Projective>, Vec<u8>)> =
        BoundedProofQueue::new(500);

    group.bench_with_input(BenchmarkId::new("prove", n_bits), &n_bits, |b, _| {
        b.iter(|| {
            let witness = RangeWitness::<Fr>::new(Fr::from(rng.next_u64()), n_bits, rng);
            let statement = RangeStatement::<Projective>::new(crs, &witness);
            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&[statement.v]).unwrap();
            prover_state.ratchet().unwrap();
            let proof = range_prove::<Projective, _>(prover_state, crs, &witness, rng).unwrap();
            proofs.push((statement.clone(), proof));
        })
    });

    group.bench_with_input(BenchmarkId::new("verify", n_bits), &n_bits, |b, _| {
        b.iter(|| {
            let (statement, proof) = proofs.choose(rng).unwrap();
            let mut verifier_state = domain_separator.to_verifier_state(proof);
            verifier_state.public_points(&[statement.v]).unwrap();
            verifier_state.ratchet().unwrap();
            range_verify::<Projective>(&mut verifier_state, crs, statement).unwrap();
        })
    });

    group.finish();
}

fn bench_range_proofs(c: &mut Criterion) {
    let mut rng = OsRng;
    // Create shared CRS that's large enough for all range proof sizes we want to test
    let shared_crs = RangeCRS::rand(64, &mut rng);

    [8, 16, 32, 64].iter().for_each(|&n_bits| {
        bench_range_prove_verify_cycle(c, &shared_crs, n_bits, &mut rng);
    });
}

criterion_group!(range_benches, bench_range_proofs);
criterion_main!(range_benches);
