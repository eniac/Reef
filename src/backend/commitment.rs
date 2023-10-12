type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

use crate::backend::costs::logmn;
use crate::backend::merkle_tree::MerkleCommitment;
use crate::backend::nova::int_to_ff;
use crate::backend::r1cs_helper::verifier_mle_eval;
use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use circ::cfg::cfg;
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
        ipa_pc::{InnerProductArgument, InnerProductInstance, InnerProductWitness},
        pedersen::{Commitment, CommitmentGens, CompressedCommitment},
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
    },
    spartan::direct::{SpartanProverKey, SpartanSNARK, SpartanVerifierKey},
    traits::{
        circuit::StepCircuit, commitment::*, evaluation::GetGeneratorsTrait, AbsorbInROTrait,
        Group, ROConstantsTrait, ROTrait,
    },
    StepCounterType,
};
use pasta_curves::{
    self,
    arithmetic::{CurveAffine, CurveExt, Group as OtherGroup},
    group::{cofactor::CofactorCurveAffine, Curve, Group as AnotherGroup, GroupEncoding},
    pallas, vesta, Ep, EpAffine, Eq, EqAffine,
};
use rand::rngs::OsRng;
use rug::{integer::Order, ops::RemRounding, Integer};

pub struct ReefCommitment {
    pub nldoc: Option<NLDocCommitment>,
    pub merkle: Option<MerkleCommitment<<G1 as Group>::Scalar>>,
}

pub struct NLDocCommitment {
    // commitment to doc
    pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
    vector_gens: CommitmentGens<G1>,
    single_gens: CommitmentGens<G1>,
    mle_doc: Vec<<G1 as Group>::Scalar>,
    doc_commit: CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
    doc_decommit: <G1 as Group>::Scalar,
    pub doc_commit_hash: <G1 as Group>::Scalar,
    pub hash_salt: <G1 as Group>::Scalar,
    // consistency verification
    cap_pk: SpartanProverKey<G1, EE1>,
    cap_vk: SpartanVerifierKey<G1, EE1>,
    doc_len: usize,
}

pub struct ConsistencyProof {
    // consistency verification
    pub hash_d: <G1 as Group>::Scalar,
    circuit: ConsistencyCircuit<<G1 as Group>::Scalar>,
    snark: SpartanSNARK<G1, EE1, ConsistencyCircuit<<G1 as Group>::Scalar>>,
    v_commit: Commitment<G1>,
    // dot prod verification
    ipi: InnerProductInstance<G1>,
    ipa: InnerProductArgument<G1>,
    t_vp_gens: Option<CommitmentGens<G1>>,
    hybrid_ipi: Option<InnerProductInstance<G1>>,
    hybrid_ipa: Option<InnerProductArgument<G1>>,
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
        // keys for the H(s||v) proof later
        // need empty circuit
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

        let mut doc_ext: Vec<Integer> = doc.into_iter().map(|x| Integer::from(x)).collect();
        doc_ext.append(&mut vec![Integer::from(0); doc_ext_len - doc_ext.len()]);

        // println!("DOC COMMITMENT {:#?}", doc_ext.clone());
        let mle = mle_from_pts(doc_ext);

        let single_gen = cap_pk.pk.gens.get_scalar_gen();
        let vector_gen = CommitmentGens::<G1>::new_with_blinding_gen(
            b"vector_gen_doc",
            mle.len(),
            &single_gen.get_blinding_gen(),
        );

        let blind = <G1 as Group>::Scalar::random(&mut OsRng);

        let scalars: Vec<<G1 as Group>::Scalar> = //<G1 as Group>::Scalar> =
                mle.into_iter().map(|x| int_to_ff(x)).collect();

        let commit_doc = <G1 as Group>::CE::commit(&vector_gen, &scalars, &blind);

        // for in-circuit fiat shamir
        let mut ro: PoseidonRO<<G2 as Group>::Scalar, <G1 as Group>::Scalar> =
            PoseidonRO::new(PoseidonConstantsCircuit::new(), 3);
        commit_doc.absorb_in_ro(&mut ro);
        let commit_doc_hash = ro.squeeze(256); // todo

        return Self {
            pc: pc.clone(),
            vector_gens: vector_gen.clone(),
            single_gens: single_gen.clone(),
            mle_doc: scalars,
            doc_commit: commit_doc.compress(),
            doc_decommit: blind,
            doc_commit_hash: commit_doc_hash,
            hash_salt: salt,
            cap_pk,
            cap_vk,
            doc_len: doc_ext_len,
        };
    }

    pub fn prove_consistency(
        &self,
        table: &Vec<Integer>,
        proj_doc_len: usize,
        q: Vec<Integer>, //<G1 as Group>::Scalar>,
        v: Integer,      //<G1 as Group>::Scalar,
        proj: bool,
        hybrid: bool,
    ) -> ConsistencyProof {
        let v_ff = int_to_ff(v);
        let q_ff = q.clone().into_iter().map(|x| int_to_ff(x)).collect();

        let cap_d = calc_d(&[v_ff, self.hash_salt], &self.pc);
        let cap_z = vec![cap_d];

        let (ipi, ipa, v_commit, v_decommit, v_prime_commit, v_prime_decommit, v_prime) =
            self.proof_dot_prod_prover(q_ff, v_ff, proj_doc_len, proj, hybrid);

        println!("post proof dot prod prover");
        let (t_vp_gens, hybrid_ipi, hybrid_ipa) = if !hybrid {
            (None, None, None)
        } else {
            // calculate t
            let q_prime = &q[1..]; // wonder if this is okay in combo with projections?
            let t = int_to_ff(verifier_mle_eval(table, q_prime));
            let q0 = int_to_ff(q[0].clone());

            let (gens, ipi, ipa) = self.proof_hybrid_combo(
                t,
                q0,
                v_ff,
                v_commit,
                v_decommit,
                v_prime,
                v_prime_commit.unwrap(),
                v_prime_decommit.unwrap(),
            );
            (Some(gens), Some(ipi), Some(ipa))
        };

        // CAP circuit
        let cap_circuit: ConsistencyCircuit<<G1 as Group>::Scalar> =
            ConsistencyCircuit::new(&self.pc, cap_d, v_ff, self.hash_salt);

        println!("post new cap");
        let cap_res = SpartanSNARK::cap_prove(
            &self.cap_pk,
            cap_circuit.clone(),
            &cap_z,
            &v_commit.compress(),
            &v_ff,
            &v_decommit,
        );
        println!("post cap prove");
        assert!(cap_res.is_ok());

        let cap_snark = cap_res.unwrap();

        // set params
        return ConsistencyProof {
            hash_d: cap_d,
            circuit: cap_circuit,
            snark: cap_snark,
            v_commit,
            ipi,
            ipa,
            t_vp_gens,
            hybrid_ipi,
            hybrid_ipa,
        };
    }

    fn proof_dot_prod_prover(
        &self,
        q: Vec<<G1 as Group>::Scalar>,
        running_v: <G1 as Group>::Scalar,
        proj_doc_len: usize,
        proj: bool,
        hybrid: bool,
    ) -> (
        InnerProductInstance<G1>,
        InnerProductArgument<G1>,
        Commitment<G1>,
        <G1 as Group>::Scalar,
        Option<Commitment<G1>>,
        Option<<G1 as Group>::Scalar>,
        <G1 as Group>::Scalar,
    ) {
        let mut p_transcript = Transcript::new(b"dot_prod_proof");

        // println!("Q IN {:#?}", q.clone());

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

        // println!("HYBRID Q {:#?}", q_hybrid.clone());

        //println!("PROJECTIONS OLD Q {:#?}", q.clone());
        // println!("DOC LENGS {:#?} {:#?}", self.doc_len, proj_doc_len);
        let new_q = if proj {
            let mut q_add = proj_prefix(proj_doc_len, self.doc_len);
            q_add.extend(q_hybrid);
            //println!("PROJECTIONS NEW Q {:#?}", q_add.clone());
            q_add
        } else {
            q_hybrid
        };

        // println!("PROJECTIONS + HYBRID Q {:#?}", new_q);

        let q_rev = new_q.into_iter().rev().collect(); // todo get rid clone
        let running_q = q_to_mle_q(&q_rev, self.doc_len);

        // set up
        let decommit_running_v = <G1 as Group>::Scalar::random(&mut OsRng);
        let commit_running_v =
            <G1 as Group>::CE::commit(&self.single_gens, &[running_v.clone()], &decommit_running_v);
        // println!("V = {:#?}", running_v.clone());

        let (decommit_v_prime, commit_v_prime, v_prime) = if !hybrid {
            // v' == v when not hybrid
            (None, None, running_v.clone())
        } else {
            let mut v_prime = <G1 as Group>::Scalar::zero();
            for i in 0..self.mle_doc.len() {
                v_prime += &self.mle_doc[i].clone() * running_q[i].clone();
            }
            // println!("V PRIME {:#?}", v_prime);

            let decommit_v_prime = <G1 as Group>::Scalar::random(&mut OsRng);
            let commit_v_prime =
                <G1 as Group>::CE::commit(&self.single_gens, &[v_prime.clone()], &decommit_v_prime);

            (Some(decommit_v_prime), Some(commit_v_prime), v_prime)
        };

        // D(q) = v/v'
        let (ipi, ipw) = if !hybrid {
            let ipi: InnerProductInstance<G1> = InnerProductInstance::new(
                &self.doc_commit.decompress().unwrap(),
                &running_q,
                &commit_running_v,
            );
            let ipw = InnerProductWitness::new(
                &self.mle_doc,
                &self.doc_decommit,
                &running_v,
                &decommit_running_v,
            );

            (ipi, ipw)
        } else {
            let ipi: InnerProductInstance<G1> = InnerProductInstance::new(
                &self.doc_commit.decompress().unwrap(),
                &running_q,
                &commit_v_prime.unwrap(),
            );
            let ipw = InnerProductWitness::new(
                &self.mle_doc,
                &self.doc_decommit,
                &v_prime,
                &decommit_v_prime.unwrap(),
            );
            (ipi, ipw)
        };

        let ipa = InnerProductArgument::prove(
            &self.vector_gens,
            &self.single_gens,
            &ipi,
            &ipw,
            &mut p_transcript,
        )
        .unwrap();

        (
            ipi,
            ipa,
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
        v: <G1 as Group>::Scalar,
        v_commit: Commitment<G1>,
        v_decommit: <G1 as Group>::Scalar,
        v_prime: <G1 as Group>::Scalar,
        v_prime_commit: Commitment<G1>,
        v_prime_decommit: <G1 as Group>::Scalar,
    ) -> (
        CommitmentGens<G1>,
        InnerProductInstance<G1>,
        InnerProductArgument<G1>,
    ) {
        let mut p_transcript = Transcript::new(b"dot_prod_proof");

        // new inner prod vectors
        let q0_vec = vec![(<G1 as Group>::Scalar::from(1) - q0), q0];
        let t_vp_clear = vec![t, v_prime];

        // make new commitment to [t, v']
        // C(v') = g_0^v' * h^blind
        // C([t,v']) = g_1^t * g_0^v * h^blind
        let mut new_base = <G1 as Group>::from_label(b"new_base", 1);

        let mut bases = new_base.clone();
        bases.push(v_prime_commit.comm.to_affine());
        let t_vp_commit = Commitment {
            comm: <G1 as Group>::vartime_multiscalar_mul(
                &[t, <G1 as Group>::Scalar::from(1)],
                &bases,
            ),
        };
        let t_vp_decommit = v_prime_decommit;
        let mut t_vp_gens = self.single_gens.clone();

        new_base.extend(t_vp_gens.gens);
        t_vp_gens.gens = new_base;

        let ipi: InnerProductInstance<G1> =
            InnerProductInstance::new(&t_vp_commit, &q0_vec, &v_commit);
        let ipw = InnerProductWitness::new(&t_vp_clear, &t_vp_decommit, &v, &v_decommit);
        let ipa = InnerProductArgument::prove(
            &t_vp_gens,
            &self.single_gens,
            &ipi,
            &ipw,
            &mut p_transcript,
        )
        .unwrap();

        (t_vp_gens, ipi, ipa)
    }

    pub fn verify_consistency(&self, proof: ConsistencyProof) {
        assert!(self.proof_dot_prod_verify(&proof.ipi, proof.ipa).is_ok());

        if proof.hybrid_ipi.is_some() && proof.hybrid_ipa.is_some() {
            assert!(self
                .verify_hybrid_combo(
                    &proof.t_vp_gens.unwrap(),
                    &proof.hybrid_ipi.unwrap(),
                    proof.hybrid_ipa.unwrap(),
                )
                .is_ok());
        }

        // cap verify
        let z_0 = vec![proof.hash_d];
        let z_out = proof.circuit.output(&z_0);
        let io = z_0.into_iter().chain(z_out.into_iter()).collect::<Vec<_>>();
        let res = proof
            .snark
            .cap_verify(&self.cap_vk, &io, &proof.v_commit.compress());
        // TODO compress()

        assert!(res.is_ok());
    }

    fn proof_dot_prod_verify(
        &self,
        ipi: &InnerProductInstance<G1>,
        ipa: InnerProductArgument<G1>,
    ) -> Result<(), NovaError> {
        let mut v_transcript = Transcript::new(b"dot_prod_proof");

        ipa.verify(
            &self.vector_gens,
            &self.single_gens,
            self.doc_len,
            ipi,
            &mut v_transcript,
        )?;

        Ok(())
    }

    fn verify_hybrid_combo(
        &self,
        t_vp_gens: &CommitmentGens<G1>,
        ipi: &InnerProductInstance<G1>,
        ipa: InnerProductArgument<G1>,
    ) -> Result<(), NovaError> {
        let mut v_transcript = Transcript::new(b"dot_prod_proof");

        // prove < C(t,v'), [1-q0, q0] > = v
        ipa.verify(t_vp_gens, &self.single_gens, 2, &ipi, &mut v_transcript)?;

        Ok(())
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

fn proj_prefix(proj_doc_len: usize, doc_ext_len: usize) -> Vec<<G1 as Group>::Scalar> {
    // what's s?
    let chunk_size = proj_doc_len;
    let start = doc_ext_len - proj_doc_len;
    assert!(start % chunk_size == 0);

    let num_chunks = doc_ext_len / chunk_size;

    let mut start_idx = start / chunk_size;

    // println!(
    //     "chunk size {}, num chunks {}, s = {}",
    //     chunk_size, num_chunks, start_idx
    // );

    let mut q_add = vec![];
    for _i in 0..logmn(num_chunks) {
        q_add.push(<G1 as Group>::Scalar::from((start_idx % 2) as u64));
        start_idx = start_idx >> 1;
    }
    q_add
}

// TODO test, TODO over ff, not Integers
// calculate multilinear extension from evals of univariate
// must "pad out" pts to power of 2 !
fn mle_from_pts(pts: Vec<Integer>) -> Vec<Integer> {
    let num_pts = pts.len();
    if num_pts == 1 {
        return vec![pts[0].clone()];
    }

    let h = num_pts / 2;

    let mut l = mle_from_pts(pts[..h].to_vec());
    let mut r = mle_from_pts(pts[h..].to_vec());

    for i in 0..r.len() {
        r[i] -= &l[i];
        l.push(r[i].clone().rem_floor(cfg().field().modulus()));
    }

    l
}

fn q_to_mle_q<F: PrimeField>(q: &Vec<F>, mle_len: usize) -> Vec<F> {
    let mut q_out = vec![];
    let base: usize = 2;

    for idx in 0..mle_len {
        let mut new_term = F::from(1);
        for j in 0..q.len() {
            // for each possible var in this term
            if (idx / base.pow(j as u32)) % 2 == 1 {
                // is this var in this term?
                new_term *= q[j].clone(); // todo?
                                          // note this loop is never triggered for constant :)
            }
        }

        q_out.push(new_term); //.rem_floor(cfg().field().modulus()));
    }

    q_out
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
    fn commit() {
        // "document"
        let scalars = vec![
            <<G1 as Group>::Scalar>::from(0),
            <<G1 as Group>::Scalar>::from(1),
            <<G1 as Group>::Scalar>::from(0),
            <<G1 as Group>::Scalar>::from(1),
        ];

        let gens_t = CommitmentGens::<G1>::new(b"nlookup document commitment", scalars.len()); // n is dimension
        let decommit_doc = <G1 as Group>::Scalar::random(&mut OsRng);
        let commit_doc = <G1 as Group>::CE::commit(&gens_t, &scalars, &decommit_doc);

        let running_q = vec![
            <<G1 as Group>::Scalar>::from(2),
            <<G1 as Group>::Scalar>::from(3),
            <<G1 as Group>::Scalar>::from(5),
            <<G1 as Group>::Scalar>::from(7),
        ];

        let running_v = <<G1 as Group>::Scalar>::from(10);

        // sanity
        let mut sum = <G1 as Group>::Scalar::zero();
        for i in 0..scalars.len() {
            sum += scalars[i].clone() * running_q[i].clone();
        }
        // this passes
        assert_eq!(sum, running_v); // <MLE_scalars * running_q> = running_v

        // proof of dot prod
        let mut p_transcript = Transcript::new(b"dot_prod_proof");
        let mut v_transcript = Transcript::new(b"dot_prod_proof");

        // set up
        let gens_single =
            CommitmentGens::<G1>::new_with_blinding_gen(b"gens_s", 1, &gens_t.get_blinding_gen());
        let decommit_running_v = <G1 as Group>::Scalar::random(&mut OsRng);
        let commit_running_v =
            <G1 as Group>::CE::commit(&gens_single, &[running_v.clone()], &decommit_running_v);

        // prove
        let ipi: InnerProductInstance<G1> =
            InnerProductInstance::new(&commit_doc, &running_q, &commit_running_v);
        let ipw =
            InnerProductWitness::new(&scalars, &decommit_doc, &running_v, &decommit_running_v);
        let ipa = InnerProductArgument::prove(&gens_t, &gens_single, &ipi, &ipw, &mut p_transcript);

        // verify
        let num_vars = running_q.len();

        let res = ipa
            .unwrap()
            .verify(&gens_t, &gens_single, num_vars, &ipi, &mut v_transcript);

        assert!(res.is_ok());
    }

    #[test]
    fn mle_q_ext() {
        init();
        let uni: Vec<Integer> = vec![
            Integer::from(60),
            Integer::from(80),
            Integer::from(9),
            Integer::from(4),
            Integer::from(77),
            Integer::from(18),
            Integer::from(24),
            Integer::from(10),
        ];

        let mle = mle_from_pts(uni.clone());

        // 011 = 6
        //let q = vec![Integer::from(0), Integer::from(1), Integer::from(1)];
        let q = vec![
            <G1 as Group>::Scalar::from(2),
            <G1 as Group>::Scalar::from(3),
            <G1 as Group>::Scalar::from(5),
        ];

        let mut mle_f: Vec<<G1 as Group>::Scalar> = vec![];
        for m in &mle {
            mle_f.push(int_to_ff(m.clone()));
        }

        let q_ext = q_to_mle_q(&q, mle_f.len());

        assert_eq!(mle_f.len(), q_ext.len());
        // inner product
        let mut sum = <G1 as Group>::Scalar::zero();
        for i in 0..mle.len() {
            sum += mle_f[i].clone() * q_ext[i].clone();
        }
        assert_eq!(sum, <G1 as Group>::Scalar::from(1162));
    }

    #[test]
    fn projections() {
        init();
        let uni: Vec<Integer> = vec![
            Integer::from(60), // 000
            Integer::from(80), // 001
            Integer::from(9),  // 010
            Integer::from(4),  // 011
            Integer::from(77), // 100
            Integer::from(18), // 101
            Integer::from(24), // 110
            Integer::from(10), // 111
        ];
        let mle = mle_from_pts(uni.clone());
        let mut mle_f: Vec<<G1 as Group>::Scalar> = vec![];
        for m in &mle {
            mle_f.push(int_to_ff(m.clone()));
        }

        let uni_sub: Vec<Integer> = vec![
            Integer::from(77), // 100
            Integer::from(18), // 101
            Integer::from(24), // 110
            Integer::from(10), // 111
        ];
        let mle_sub = mle_from_pts(uni_sub.clone());
        let mut mle_sub_f: Vec<<G1 as Group>::Scalar> = vec![];
        for m in &mle_sub {
            mle_sub_f.push(int_to_ff(m.clone()));
        }

        // 011 = 6
        //let q = vec![Integer::from(0), Integer::from(1), Integer::from(1)];
        let q = vec![
            <G1 as Group>::Scalar::zero(),
            <G1 as Group>::Scalar::from(1),
            <G1 as Group>::Scalar::from(1), // selector
        ];
        let q_ext = q_to_mle_q(&q, mle_f.len());
        assert_eq!(mle_f.len(), q_ext.len());
        // inner product
        let mut sum = <G1 as Group>::Scalar::zero();
        for i in 0..mle.len() {
            sum += mle_f[i].clone() * q_ext[i].clone();
        }

        let q_sub = vec![
            <G1 as Group>::Scalar::zero(),
            <G1 as Group>::Scalar::from(1),
        ];
        let q_ext_sub = q_to_mle_q(&q_sub, mle_sub_f.len());
        assert_eq!(mle_sub_f.len(), q_ext_sub.len());

        // inner product
        let mut sum_sub = <G1 as Group>::Scalar::zero();
        for i in 0..mle_sub.len() {
            sum_sub += mle_sub_f[i].clone() * q_ext_sub[i].clone();
        }
        assert_eq!(sum, sum_sub);

        //    println!("SUM {:#?}", sum.clone());
    }

    #[test]
    fn hybrid() {
        init();
        let uni: Vec<Integer> = vec![
            Integer::from(60), // 000
            Integer::from(80), // 001
            Integer::from(9),  // 010
            Integer::from(4),  // 011
            Integer::from(77), // 100
            Integer::from(18), // 101
            Integer::from(24), // 110
            Integer::from(10), // 111
        ];
        let mle = mle_from_pts(uni.clone());
        let mut mle_f: Vec<<G1 as Group>::Scalar> = vec![];
        for m in &mle {
            mle_f.push(int_to_ff(m.clone()));
        }

        let uni_sub: Vec<Integer> = vec![
            Integer::from(77), // 100
            Integer::from(18), // 101
            Integer::from(24), // 110
            Integer::from(10), // 111
        ];
        let mle_sub = mle_from_pts(uni_sub.clone());
        let mut mle_sub_f: Vec<<G1 as Group>::Scalar> = vec![];
        for m in &mle_sub {
            mle_sub_f.push(int_to_ff(m.clone()));
        }

        // 011 = 6
        //let q = vec![Integer::from(0), Integer::from(1), Integer::from(1)];
        let q = vec![
            <G1 as Group>::Scalar::from(2),
            <G1 as Group>::Scalar::from(3),
            <G1 as Group>::Scalar::from(5), // selector
        ];

        let q_ext = q_to_mle_q(&q, mle_f.len());
        assert_eq!(mle_f.len(), q_ext.len());
        // inner product
        let mut v = <G1 as Group>::Scalar::zero();
        for i in 0..mle.len() {
            v += mle_f[i].clone() * q_ext[i].clone();
        }

        let q_sub = vec![
            <G1 as Group>::Scalar::from(2),
            <G1 as Group>::Scalar::from(3),
        ];
        let q_ext_sub = q_to_mle_q(&q_sub, mle_sub_f.len());
        assert_eq!(mle_sub_f.len(), q_ext_sub.len());

        // inner product
        let mut v_sub = <G1 as Group>::Scalar::zero();
        for i in 0..mle_sub.len() {
            v_sub += mle_sub_f[i].clone() * q_ext_sub[i].clone();
        }

        let table: Vec<Integer> = vec![
            Integer::from(60), // 000
            Integer::from(80), // 001
            Integer::from(9),  // 010
            Integer::from(4),  // 011
        ];
        let mle_table = mle_from_pts(table.clone());
        let mut mle_table_f: Vec<<G1 as Group>::Scalar> = vec![];
        for m in &mle_table {
            mle_table_f.push(int_to_ff(m.clone()));
        }

        let mut t = <G1 as Group>::Scalar::zero();
        for i in 0..mle_sub.len() {
            t += mle_table_f[i].clone() * q_ext_sub[i].clone();
        }

        // println!("t {:#?}, v' {:#?}, v {:#?}", t, v_sub, v);

        assert_eq!(
            v,
            t * (<G1 as Group>::Scalar::from(1) - q[2]) + v_sub * q[2]
        );
    }
}
