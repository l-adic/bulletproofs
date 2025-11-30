pub mod common;

use ark_secp256k1::Projective;
use bulletproofs::{
    ipa::{
        prove as ipa_prove,
        types::{CRS as IpaCRS, CrsSize, Statement as IpaStatement, Witness as IpaWitness},
        verify as ipa_verify, verify_aux,
    },
    msm::verify_batch_aux,
};
use common::BoundedProofQueue;
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use nonempty::NonEmpty;
use rand::rngs::OsRng;
use rayon::prelude::*;

struct ProofData {
    proof: Vec<u8>,
}

const BATCH_SIZE: usize = 100;

fn bench_ipa_prove_verify_cycle<Rng: rand::Rng>(
    c: &mut Criterion,
    crs: &IpaCRS<Projective>,
    witness_log2_size: usize,
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group("ipa");
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(80));

    let witness_size = 2_usize.pow(witness_log2_size as u32);

    let mut proofs: BoundedProofQueue<(IpaStatement<Projective>, ProofData)> =
        BoundedProofQueue::new(500);

    group.bench_with_input(
        BenchmarkId::new("prove", witness_log2_size),
        &witness_log2_size,
        |b, _| {
            b.iter(|| {
                let witness = IpaWitness::rand(witness_size as u64, rng);
                let stmt = witness.statement(crs);

                let domain_separator =
                    spongefish::domain_separator!("ipa-benchmark").instance(&stmt);
                let mut prover_state = domain_separator.std_prover();

                let proof = ipa_prove(&mut prover_state, crs, stmt, &witness);
                let proof_input = ProofData { proof };
                proofs.push((stmt, proof_input));
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("verify", witness_log2_size),
        &witness_log2_size,
        |b, _| {
            b.iter(|| {
                let (stmt, proof) = proofs.choose(rng).unwrap();
                let domain_separator =
                    spongefish::domain_separator!("ipa-benchmark").instance(&stmt);
                let mut verifier_state = domain_separator.std_verifier(&proof.proof);
                ipa_verify(&mut verifier_state, crs, stmt).unwrap();
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("verify_batch", witness_log2_size),
        &witness_log2_size,
        |b, _| {
            b.iter(|| {
                let selected_proofs = proofs.choose_multiple(rng, BATCH_SIZE);

                let verifications = selected_proofs
                    .into_par_iter()
                    .map(|(statement, ProofData { proof })| {
                        let domain_separator =
                            spongefish::domain_separator!("ipa-benchmark").instance(statement);
                        let mut verifier_state = domain_separator.std_verifier(proof);
                        verify_aux(&mut verifier_state, crs, statement)
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();

                let verifications = NonEmpty::from_vec(verifications).expect("non-empty vec");
                verify_batch_aux(verifications, &mut OsRng).expect("should verify batch");
                black_box(())
            })
        },
    );

    group.finish();
}

fn bench_ipa_proofs(c: &mut Criterion) {
    let mut rng = OsRng;
    let crs_size = CrsSize { log2_size: 16 };
    let crs: IpaCRS<Projective> = IpaCRS::rand(crs_size, &mut rng);

    for witness_log2_size in [2, 4, 8, 16] {
        bench_ipa_prove_verify_cycle(c, &crs, witness_log2_size, &mut rng);
    }
}

criterion_group!(ipa_benches, bench_ipa_proofs);
criterion_main!(ipa_benches);
