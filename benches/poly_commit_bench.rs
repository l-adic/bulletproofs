pub mod common;

use ark_ec::PrimeGroup;
use ark_poly::univariate::DensePolynomial;
use ark_secp256k1::Projective;
use ark_std::UniformRand;
use bulletproofs::{
    ipa::types::CrsSize,
    poly_commit::{
        OpeningProofDomainSeparator, Todo, fold_todos_statement, fold_todos_witness, lazy_verify,
        prove as poly_prove,
        types::{CRS, Statement, Witness},
        verify as poly_verify,
    },
};
use common::BoundedProofQueue;
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use rand::rngs::OsRng;
use spongefish::{
    DomainSeparator,
    codecs::arkworks_algebra::{CommonFieldToUnit, CommonGroupToUnit},
};

type Fr = <ark_ec::short_weierstrass::Projective<ark_secp256k1::Config> as PrimeGroup>::ScalarField;

struct ProofData {
    proof: Vec<u8>,
    statement: Statement<Projective>,
    todo: Todo<Projective>,
}

const BATCH_SIZES: &[usize] = &[10, 100];

fn bench_single_poly_commit<Rng: rand::Rng>(
    c: &mut Criterion,
    crs_log2_size: usize,
    crs: &CRS<Projective>,
    rng: &mut Rng,
) -> BoundedProofQueue<(ProofData, DomainSeparator)> {
    let mut group = c.benchmark_group("poly_commit_single");
    group.sample_size(10);

    let poly_degree = crs.size() - 1;

    let domain_separator = {
        let domain_separator = DomainSeparator::new("poly-commit-benchmark");
        let domain_separator =
            OpeningProofDomainSeparator::<Projective>::opening_proof_statement(domain_separator)
                .ratchet();
        OpeningProofDomainSeparator::<Projective>::add_opening_proof(domain_separator, crs.size())
    };

    let mut proofs: BoundedProofQueue<(ProofData, DomainSeparator)> = BoundedProofQueue::new(500);

    group.bench_with_input(
        BenchmarkId::new("prove", crs_log2_size),
        &crs_log2_size,
        |b, _| {
            b.iter(|| {
                let witness: Witness<Projective, DensePolynomial<Fr>> =
                    Witness::rand(poly_degree, rng);
                let x = Fr::rand(rng);
                let statement = witness.statement(crs, x);

                let mut prover_state = domain_separator.to_prover_state();
                prover_state
                    .public_points(&[statement.commitment.g])
                    .unwrap();
                prover_state.public_scalars(&[statement.x]).unwrap();
                prover_state
                    .public_scalars(&[statement.evaluation])
                    .unwrap();
                prover_state.ratchet().unwrap();

                let todo = poly_prove(&mut prover_state, crs, &statement, &witness, rng).unwrap();
                let proof_data = ProofData {
                    proof: prover_state.narg_string().to_vec(),
                    statement,
                    todo,
                };
                proofs.push((proof_data, domain_separator.clone()));
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("verify", crs_log2_size),
        &crs_log2_size,
        |b, _| {
            b.iter(|| {
                let (proof_data, domain_separator) = proofs.choose(rng).unwrap();
                let mut verifier_state = domain_separator.to_verifier_state(&proof_data.proof);
                verifier_state
                    .public_points(&[proof_data.statement.commitment.g])
                    .unwrap();
                verifier_state
                    .public_scalars(&[proof_data.statement.x])
                    .unwrap();
                verifier_state
                    .public_scalars(&[proof_data.statement.evaluation])
                    .unwrap();
                verifier_state.ratchet().unwrap();
                poly_verify(&mut verifier_state, crs, &proof_data.statement).unwrap();
            })
        },
    );

    group.finish();
    proofs
}

fn bench_aggregated_poly_commit<Rng: rand::Rng>(
    c: &mut Criterion,
    crs_log2_size: usize,
    crs: &CRS<Projective>,
    proofs_queue: &BoundedProofQueue<(ProofData, DomainSeparator)>,
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group("poly_commit_aggregated");
    group.sample_size(10);

    for &batch_size in BATCH_SIZES {
        group.bench_with_input(
            BenchmarkId::new(
                "lazy_verify_and_aggregate",
                format!("{}_batch_{}", crs_log2_size, batch_size),
            ),
            &batch_size,
            |b, _| {
                b.iter(|| {
                    // Select random batch of proofs from the queue
                    let selected_proofs = proofs_queue.choose_multiple(rng, batch_size);

                    // Lazy verify all proofs in the batch
                    let todos = selected_proofs
                        .iter()
                        .try_fold(Vec::new(), |todos, (proof_data, domain_separator)| {
                            let mut verifier_state =
                                domain_separator.to_verifier_state(&proof_data.proof);
                            verifier_state
                                .public_points(&[proof_data.statement.commitment.g])
                                .unwrap();
                            verifier_state
                                .public_scalars(&[proof_data.statement.x])
                                .unwrap();
                            verifier_state
                                .public_scalars(&[proof_data.statement.evaluation])
                                .unwrap();
                            verifier_state.ratchet().unwrap();

                            lazy_verify(
                                &mut verifier_state,
                                crs,
                                &proof_data.statement,
                                proof_data.todo.g,
                                todos,
                            )
                        })
                        .unwrap();

                    // Aggregate and verify the final proof
                    if !todos.is_empty() {
                        let alpha = Fr::rand(rng);
                        let x = Fr::rand(rng);
                        let amortized_witness = fold_todos_witness(&todos, alpha);
                        let amortized_statement = fold_todos_statement(&todos, alpha, x);

                        // Use the domain separator from the first proof
                        let domain_separator = &selected_proofs[0].1;

                        // Final verification of aggregated proof
                        let mut prover_state = domain_separator.to_prover_state();
                        prover_state
                            .public_points(&[amortized_statement.commitment.g])
                            .unwrap();
                        prover_state
                            .public_scalars(&[amortized_statement.x])
                            .unwrap();
                        prover_state
                            .public_scalars(&[amortized_statement.evaluation])
                            .unwrap();
                        prover_state.ratchet().unwrap();

                        let _ = poly_prove(
                            &mut prover_state,
                            crs,
                            &amortized_statement,
                            &amortized_witness,
                            rng,
                        )
                        .unwrap();

                        let mut verifier_state =
                            domain_separator.to_verifier_state(prover_state.narg_string());
                        verifier_state
                            .public_points(&[amortized_statement.commitment.g])
                            .unwrap();
                        verifier_state
                            .public_scalars(&[amortized_statement.x])
                            .unwrap();
                        verifier_state
                            .public_scalars(&[amortized_statement.evaluation])
                            .unwrap();
                        verifier_state.ratchet().unwrap();
                        poly_verify(&mut verifier_state, crs, &amortized_statement).unwrap();
                    }

                    black_box(())
                })
            },
        );
    }

    group.finish();
}

fn bench_poly_commit_proofs(c: &mut Criterion) {
    let mut rng = OsRng;

    // Test various CRS sizes: 2^4, 2^8, 2^12, 2^16
    for crs_log2_size in [4, 8, 12, 16] {
        println!(
            "Generating CRS of size 2^{} = {}",
            crs_log2_size,
            1 << crs_log2_size
        );
        let crs_size = CrsSize {
            log2_size: crs_log2_size as u64,
        };
        let crs: CRS<Projective> = CRS::rand(crs_size, &mut rng);

        let proofs = bench_single_poly_commit(c, crs_log2_size, &crs, &mut rng);
        bench_aggregated_poly_commit(c, crs_log2_size, &crs, &proofs, &mut rng);
    }
}

criterion_group!(poly_commit_benches, bench_poly_commit_proofs);
criterion_main!(poly_commit_benches);
