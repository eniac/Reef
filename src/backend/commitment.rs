type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

use crate::backend::merkle_tree::MerkleCommitment;
use crate::backend::nova::int_to_ff;
use crate::backend::r1cs_helper::verifier_mle_eval;
use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use generic_array::typenum;
use merlin::Transcript;
use neptune::{
    circuit2::Elt,
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
};
use nova_snark::{
    errors::NovaError,
    provider::{
        hyrax_pc::{HyraxPC, PolyCommit, PolyCommitBlinds},
        ipa_pc::InnerProductArgument,
        pedersen::{CommitmentGens, CompressedCommitment},
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
    },
    spartan::{
        direct::{SpartanProverKey, SpartanSNARK, SpartanVerifierKey},
        nizk::EqualityProof,
        polynomial::{EqPolynomial, MultilinearPolynomial},
    },
    traits::{
        circuit::StepCircuit, commitment::*, evaluation::GetGeneratorsTrait, AbsorbInROTrait,
        AppendToTranscriptTrait, ChallengeTrait, Group, ROConstantsTrait, ROTrait,
    },
    StepCounterType,
};
use rand::rngs::OsRng;
use rug::{integer::Order, Integer};
use serde::{Deserialize, Serialize};

#[derive(Deserialize, Serialize)]
pub struct ReefCommitment {
    pub nldoc: Option<NLDocCommitment>,
    pub merkle: Option<MerkleCommitment<<G1 as Group>::Scalar>>,
}

#[derive(Deserialize, Serialize)]
pub struct NLDocCommitment {
    // commitment to doc
    pub pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
    single_gens: CommitmentGens<G1>,
    hyrax_gen: HyraxPC<G1>,
    doc_poly: MultilinearPolynomial<<G1 as Group>::Scalar>,
    pub doc_commit: PolyCommit<G1>,
    doc_decommit: PolyCommitBlinds<G1>,
    pub doc_commit_hash: <G1 as Group>::Scalar,
    pub hash_salt: <G1 as Group>::Scalar,
    // consistency verification
    cap_pk: SpartanProverKey<G1, EE1>,
    cap_vk: SpartanVerifierKey<G1, EE1>,
}

#[derive(Deserialize, Serialize)]
pub struct ConsistencyProof {
    // consistency verification
    pub hash_d: <G1 as Group>::Scalar,
    circuit: ConsistencyCircuit<<G1 as Group>::Scalar>,
    pub snark: SpartanSNARK<G1, EE1, ConsistencyCircuit<<G1 as Group>::Scalar>>,
    pub v_commit: CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
    // dot prod verification
    pub v_prime_commit: Option<CompressedCommitment<<G1 as Group>::CompressedGroupElement>>,
    pub ipa: InnerProductArgument<G1>,
    pub running_q: Vec<<G1 as Group>::Scalar>,
    // eq proof
    pub eq_proof: Option<EqualityProof<G1>>,
    l_commit: Option<CompressedCommitment<<G1 as Group>::CompressedGroupElement>>,
}

impl ReefCommitment {
    pub fn new(
        doc: Vec<usize>,
        hybrid_len: Option<usize>,
        merkle: bool,
        pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
    ) -> Self {
        if merkle {
            Self {
                nldoc: None,
                merkle: Some(MerkleCommitment::new(&doc, pc)),
            }
        } else {
            Self {
                nldoc: Some(NLDocCommitment::new(doc, hybrid_len, pc)),
                merkle: None,
            }
        }
    }
}

impl NLDocCommitment {
    pub fn new(
        doc: Vec<usize>,
        hybrid_len: Option<usize>,
        pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
    ) -> Self
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
    {
        let cap_circuit: ConsistencyCircuit<<G1 as Group>::Scalar> = ConsistencyCircuit::new(
            &pc,
            <G1 as Group>::Scalar::zero(),
            <G1 as Group>::Scalar::zero(),
            <G1 as Group>::Scalar::zero(),
        );

        // produce CAP keys
        let (cap_pk, cap_vk) =
            SpartanSNARK::<G1, EE1, ConsistencyCircuit<<G1 as Group>::Scalar>>::setup(
                cap_circuit.clone(),
            )
            .unwrap();

        // salf for H(s||v) proof
        let salt = <G1 as Group>::Scalar::random(&mut OsRng);

        // commitment to document
        let doc_ext_len = if hybrid_len.is_some() {
            hybrid_len.unwrap() / 2
        } else {
            doc.len().next_power_of_two()
        };

        let mut doc_ext: Vec<<G1 as Group>::Scalar> = doc
            .into_iter()
            .map(|x| <G1 as Group>::Scalar::from(x as u64))
            .collect();

        if doc_ext_len > doc_ext.len() {
            doc_ext.append(&mut vec![
                <G1 as Group>::Scalar::zero();
                doc_ext_len - doc_ext.len()
            ]);
        }
        let poly = MultilinearPolynomial::new(doc_ext);

        let single_gen = cap_pk.pk.gens.get_scalar_gen();

        let (_left, right) =
            EqPolynomial::<<G1 as Group>::Scalar>::compute_factored_lens(poly.get_num_vars());

        let vector_gen = CommitmentGens::<G1>::new_with_blinding_gen(
            b"vector_gen_doc",
            (2usize).pow(right as u32),
            &single_gen.get_blinding_gen(),
        );

        let hyrax_gen = HyraxPC {
            gens_v: vector_gen.clone(),
            gens_s: single_gen.clone(),
        };

        let (doc_commit, doc_decommit) = hyrax_gen.commit(&poly);

        // for in-circuit fiat shamir
        let mut ro: PoseidonRO<<G2 as Group>::Scalar, <G1 as Group>::Scalar> =
            PoseidonRO::new(PoseidonConstantsCircuit::new(), doc_commit.comm.len() * 3);
        for c in 0..doc_commit.comm.len() {
            let cc: CompressedCommitment<<G1 as Group>::CompressedGroupElement> =
                doc_commit.comm[c];
            let dc = cc.decompress().unwrap();
            dc.absorb_in_ro(&mut ro);
        }
        let commit_doc_hash = ro.squeeze(256);

        return Self {
            pc: pc.clone(),
            single_gens: single_gen.clone(),
            hyrax_gen,
            doc_poly: poly,
            doc_commit,
            doc_decommit,
            doc_commit_hash: commit_doc_hash,
            hash_salt: salt,
            cap_pk,
            cap_vk,
        };
    }

    pub fn prove_consistency(
        &self,
        table: &Vec<Integer>,
        proj_chunk_idx: Option<Vec<usize>>,
        q: Vec<Integer>,
        v: Integer,
        proj: bool,
        hybrid: bool,
    ) -> ConsistencyProof {
        let v_ff = int_to_ff(v);
        let q_ff = q.clone().into_iter().map(|x| int_to_ff(x)).collect();

        let cap_d = calc_d(&[v_ff, self.hash_salt], &self.pc);
        let cap_z = vec![cap_d];

        let (ipa, running_q, v_commit, v_decommit, v_prime_commit, v_prime_decommit, v_prime) =
            self.proof_dot_prod_prover(q_ff, v_ff, proj_chunk_idx, proj, hybrid);

        let (eq_proof, l_commit) = if !hybrid {
            (None, None)
        } else {
            // calculate t
            let q_prime = &q[1..];
            let t = int_to_ff(verifier_mle_eval(table, q_prime));
            let q0 = int_to_ff(q[0].clone());

            assert_eq!(
                (<G1 as Group>::Scalar::from(1) - q0) * t + q0 * v_prime,
                v_ff
            );

            let (eq_proof, l_commit) = self.proof_hybrid_combo(
                t,
                q0,
                v_commit,
                v_decommit,
                v_prime_commit.unwrap(),
                v_prime_decommit.unwrap(),
            );
            (Some(eq_proof), Some(l_commit))
        };

        // CAP circuit
        let cap_circuit: ConsistencyCircuit<<G1 as Group>::Scalar> =
            ConsistencyCircuit::new(&self.pc, cap_d, v_ff, self.hash_salt);

        let cap_res = SpartanSNARK::cap_prove(
            &self.cap_pk,
            cap_circuit.clone(),
            &cap_z,
            &v_commit,
            &v_ff,
            &v_decommit,
        );
        assert!(cap_res.is_ok());

        let cap_snark = cap_res.unwrap();

        // set params
        return ConsistencyProof {
            hash_d: cap_d,
            circuit: cap_circuit,
            snark: cap_snark,
            v_commit,
            v_prime_commit,
            ipa,
            running_q,
            eq_proof,
            l_commit,
        };
    }

    fn proof_dot_prod_prover(
        &self,
        q: Vec<<G1 as Group>::Scalar>,
        running_v: <G1 as Group>::Scalar,
        proj_chunk_idx: Option<Vec<usize>>,
        proj: bool,
        hybrid: bool,
    ) -> (
        InnerProductArgument<G1>,
        Vec<<G1 as Group>::Scalar>,
        CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
        <G1 as Group>::Scalar,
        Option<CompressedCommitment<<G1 as Group>::CompressedGroupElement>>,
        Option<<G1 as Group>::Scalar>,
        <G1 as Group>::Scalar,
    ) {
        let mut p_transcript = Transcript::new(b"dot_prod_proof");

        // hybrid
        let q_hybrid = if !hybrid {
            q
        } else {
            let mut q_prime = vec![];
            for i in 1..(q.len()) {
                q_prime.push(q[i]);
            }
            q_prime
        };

        let running_q: Vec<<G1 as Group>::Scalar> = if proj {
            let mut q_add: Vec<<G1 as Group>::Scalar> = proj_chunk_idx
                .unwrap()
                .into_iter()
                .map(|x| <G1 as Group>::Scalar::from(x as u64))
                .collect();

            q_add.extend(q_hybrid);
            q_add
        } else {
            q_hybrid
        };

        // set up
        let decommit_running_v = <G1 as Group>::Scalar::random(&mut OsRng);
        let commit_running_v =
            <G1 as Group>::CE::commit(&self.single_gens, &[running_v.clone()], &decommit_running_v)
                .compress();

        let (decommit_v_prime, commit_v_prime, v_prime) = if !hybrid {
            // v' == v when not hybrid
            (None, None, running_v.clone())
        } else {
            let v_prime = self.doc_poly.evaluate(&running_q);

            let decommit_v_prime = <G1 as Group>::Scalar::random(&mut OsRng);
            let commit_v_prime =
                <G1 as Group>::CE::commit(&self.single_gens, &[v_prime.clone()], &decommit_v_prime);

            (
                Some(decommit_v_prime),
                Some(commit_v_prime.compress()),
                v_prime,
            )
        };

        let (ipa, _, _) = if !hybrid {
            let res = self.hyrax_gen.prove_eval(
                &self.doc_poly,
                &self.doc_commit,
                &self.doc_decommit,
                &running_q,
                &running_v,
                &decommit_running_v,
                &mut p_transcript,
            );
            assert!(res.is_ok());
            res.unwrap()
        } else {
            let res = self.hyrax_gen.prove_eval(
                &self.doc_poly,
                &self.doc_commit,
                &self.doc_decommit,
                &running_q,
                &v_prime,
                &decommit_v_prime.unwrap(),
                &mut p_transcript,
            );
            assert!(res.is_ok());
            res.unwrap()
        };

        (
            ipa,
            running_q,
            commit_running_v,
            decommit_running_v,
            commit_v_prime,
            decommit_v_prime,
            v_prime,
        )
    }

    fn proof_hybrid_combo(
        &self,
        t: <G1 as Group>::Scalar,
        q0: <G1 as Group>::Scalar,
        v_commit: CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
        v_decommit: <G1 as Group>::Scalar,
        v_prime_commit: CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
        v_prime_decommit: <G1 as Group>::Scalar,
    ) -> (
        EqualityProof<G1>,
        CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
    ) {
        let r = <G1 as Group>::Scalar::random(&mut OsRng);

        let t_decommit = <G1 as Group>::Scalar::random(&mut OsRng);
        let t_commit = <G1 as Group>::CE::commit(&self.single_gens, &[t.clone()], &t_decommit);

        let l_decommit = v_prime_decommit * q0 + t_decommit * (<G1 as Group>::Scalar::from(1) - q0);
        let l_commit = (v_prime_commit.decompress().unwrap() * q0
            + t_commit * (<G1 as Group>::Scalar::from(1) - q0))
            .compress();

        let alpha =
            <G1 as Group>::CE::commit(&self.single_gens, &[<G1 as Group>::Scalar::zero()], &r)
                .compress(); // h^r

        let mut p_transcript = Transcript::new(b"eq_proof");
        p_transcript.append_message(b"protocol-name", EqualityProof::<G1>::protocol_name());
        v_commit.append_to_transcript(b"C1", &mut p_transcript);
        l_commit.append_to_transcript(b"C2", &mut p_transcript);
        alpha.append_to_transcript(b"alpha", &mut p_transcript);

        let c = <G1 as Group>::Scalar::challenge(b"c", &mut p_transcript);

        let z = c * (v_decommit - l_decommit) + r;

        (EqualityProof { alpha, z }, l_commit)
    }

    pub fn verify_consistency(&self, proof: ConsistencyProof) {
        if proof.eq_proof.is_some() && proof.l_commit.is_some() && proof.v_prime_commit.is_some() {
            assert!(self
                .proof_dot_prod_verify(&proof.ipa, &proof.running_q, &proof.v_prime_commit.unwrap())
                .is_ok());

            // equality proof C_l = C[v_r]
            let mut v_transcript = Transcript::new(b"eq_proof");
            let res = proof.eq_proof.unwrap().verify(
                &self.single_gens,
                &mut v_transcript,
                &proof.v_commit,
                &proof.l_commit.unwrap(),
            );

            assert!(res.is_ok());
        } else {
            assert!(self
                .proof_dot_prod_verify(&proof.ipa, &proof.running_q, &proof.v_commit)
                .is_ok());
        }

        // cap verify
        let z_0 = vec![proof.hash_d];
        let z_out = proof.circuit.output(&z_0);
        let io = z_0.into_iter().chain(z_out.into_iter()).collect::<Vec<_>>();
        let res = proof.snark.cap_verify(&self.cap_vk, &io, &proof.v_commit);

        assert!(res.is_ok());
    }

    fn proof_dot_prod_verify(
        &self,
        ipa: &InnerProductArgument<G1>,
        running_q: &Vec<<G1 as Group>::Scalar>,
        v_commit: &CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
    ) -> Result<(), NovaError> {
        let mut v_transcript = Transcript::new(b"dot_prod_proof");

        self.hyrax_gen.verify_eval(
            running_q,
            &self.doc_commit,
            &v_commit,
            ipa,
            &mut v_transcript,
        )
    }
}

pub fn calc_d(
    v_salt: &[<G1 as Group>::Scalar],
    pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
) -> <G1 as Group>::Scalar {
    let mut sponge = Sponge::new_with_constants(pc, Mode::Simplex);
    let acc = &mut ();

    let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
    sponge.start(parameter, None, acc);

    SpongeAPI::absorb(&mut sponge, 2, v_salt, acc);
    let d_out_vec = SpongeAPI::squeeze(&mut sponge, 1, acc);
    sponge.finish(acc).unwrap();

    d_out_vec[0]
}

pub fn final_clear_checks(
    stack_ptr: <G1 as Group>::Scalar,
    table: &Vec<Integer>,
    final_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_v: Option<<G1 as Group>::Scalar>,
) {
    // stack ptr is 0 (stack is empty)
    assert_eq!(stack_ptr, <G1 as Group>::Scalar::zero());

    if final_q.is_some() && final_v.is_some() {
        let q = final_q.unwrap();
        let v = final_v.unwrap();

        // split
        let mut q_i = vec![];
        for f in q {
            q_i.push(Integer::from_digits(f.to_repr().as_ref(), Order::Lsf));
        }
        assert_eq!(
            verifier_mle_eval(table, &q_i),
            (Integer::from_digits(v.to_repr().as_ref(), Order::Lsf))
        );
    }
}

#[derive(Clone)]
pub struct ConsistencyCircuit<F: PrimeField> {
    pc: PoseidonConstants<F, typenum::U4>,
    d: F,
    v: F,
    s: F,
}

impl<F: PrimeField> ConsistencyCircuit<F> {
    pub fn new(pc: &PoseidonConstants<F, typenum::U4>, d: F, v: F, s: F) -> Self {
        ConsistencyCircuit {
            pc: pc.clone(),
            d,
            v,
            s,
        }
    }
}

impl<F> StepCircuit<F> for ConsistencyCircuit<F>
where
    F: PrimeField,
{
    fn arity(&self) -> usize {
        1
    }

    fn output(&self, z: &[F]) -> Vec<F> {
        assert_eq!(z[0], self.d);
        z.to_vec()
    }

    #[allow(clippy::let_and_return)]
    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let d_in = z[0].clone();

        //v at index 0 (but technically 1 since io is allocated first)
        let alloc_v = AllocatedNum::alloc(cs.namespace(|| "v"), || Ok(self.v))?;
        let alloc_s = AllocatedNum::alloc(cs.namespace(|| "s"), || Ok(self.s))?;

        //poseidon(v,s) == d
        let d_calc = {
            let acc = &mut cs.namespace(|| "d hash circuit");
            let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);

            sponge.start(
                IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
                None,
                acc,
            );
            SpongeAPI::absorb(
                &mut sponge,
                2,
                &[Elt::Allocated(alloc_v.clone()), Elt::Allocated(alloc_s)],
                acc,
            );

            let output = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();
            let out =
                Elt::ensure_allocated(&output[0], &mut acc.namespace(|| "ensure allocated"), true)?;
            out
        };

        // sanity
        if d_calc.get_value().is_some() {
            assert_eq!(d_in.get_value().unwrap(), d_calc.get_value().unwrap());
        }

        cs.enforce(
            || "d == d",
            |z| z + d_in.get_variable(),
            |z| z + CS::one(),
            |z| z + d_calc.get_variable(),
        );

        Ok(vec![d_calc]) // doesn't hugely matter
    }

    fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::Incremental
    }
}

#[cfg(test)]
mod tests {

    use crate::backend::commitment::*;
    use crate::backend::nova::int_to_ff;
    use crate::backend::r1cs_helper::init;
    use rug::Integer;
    type G1 = pasta_curves::pallas::Point;

    #[test]
    fn eq_proof() {
        let gen = CommitmentGens::<G1>::new(b"gens_s", 1);

        let t = <G1 as Group>::Scalar::from(3);
        let v_prime = <G1 as Group>::Scalar::from(5);
        let q0 = <G1 as Group>::Scalar::from(7);
        let v = v_prime * q0 + t * (<G1 as Group>::Scalar::from(1) - q0);

        let v_decommit = <G1 as Group>::Scalar::random(&mut OsRng);
        let v_prime_decommit = <G1 as Group>::Scalar::random(&mut OsRng);
        let t_decommit = <G1 as Group>::Scalar::random(&mut OsRng);

        let r = <G1 as Group>::Scalar::random(&mut OsRng);

        let v_commit = <G1 as Group>::CE::commit(&gen, &[v.clone()], &v_decommit).compress();
        let v_prime_commit =
            <G1 as Group>::CE::commit(&gen, &[v_prime.clone()], &v_prime_decommit).compress();
        let t_commit = <G1 as Group>::CE::commit(&gen, &[t.clone()], &t_decommit);

        let l_decommit = v_prime_decommit * q0 + t_decommit * (<G1 as Group>::Scalar::from(1) - q0);
        let l_commit = (v_prime_commit.decompress().unwrap() * q0
            + t_commit * (<G1 as Group>::Scalar::from(1) - q0))
            .compress();

        // innards of function - PROVE
        let alpha =
            <G1 as Group>::CE::commit(&gen, &[<G1 as Group>::Scalar::zero()], &r).compress(); // h^r

        let mut p_transcript = Transcript::new(b"eq_proof");
        p_transcript.append_message(b"protocol-name", EqualityProof::<G1>::protocol_name());
        v_commit.append_to_transcript(b"C1", &mut p_transcript);
        l_commit.append_to_transcript(b"C2", &mut p_transcript);
        alpha.append_to_transcript(b"alpha", &mut p_transcript);

        let c = <G1 as Group>::Scalar::challenge(b"c", &mut p_transcript);

        let z = c * (v_decommit - l_decommit) + r;

        let eq_proof: EqualityProof<G1> = EqualityProof { alpha, z };

        // VERIFY
        // equality proof C_l = C[v_r]
        let mut v_transcript = Transcript::new(b"eq_proof");
        let res = eq_proof.verify(&gen, &mut v_transcript, &v_commit, &l_commit);

        assert!(res.is_ok());
    }
}
