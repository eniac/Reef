type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use crate::backend::costs::{JBatching, JCommit};
use crate::backend::nova::int_to_ff;
use crate::backend::r1cs_helper::{init, verifier_mle_eval};
use circ::cfg::cfg;
use ff::{Field, PrimeField};
use generic_array::typenum;
use merlin::Transcript;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
};
use nova_snark::{
    errors::NovaError,
    provider::{
        ipa_pc::{InnerProductArgument, InnerProductInstance, InnerProductWitness},
        pedersen::{Commitment, CommitmentGens},
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
    },
    traits::{commitment::*, AbsorbInROTrait, Group, ROConstantsTrait, ROTrait},
};
use rand::rngs::OsRng;
use rug::{
    integer::Order,
    ops::{RemRounding, RemRoundingAssign},
    Assign, Integer,
};

#[derive(Debug, Clone)]
pub enum ReefCommitment<F: PrimeField> {
    HashChain(HashCommitmentStruct<F>),
    Nlookup(DocCommitmentStruct<F>),
}

#[derive(Debug, Clone)]
pub struct HashCommitmentStruct<F: PrimeField> {
    pub commit: F, // <G1 as Group>::Scalar,
    pub blind: F,  // <G1 as Group>::Scalar,
}

#[derive(Debug, Clone)]
pub struct DocCommitmentStruct<F: PrimeField> {
    gens: CommitmentGens<G1>,
    gens_single: CommitmentGens<G1>,
    commit_doc: Commitment<G1>, // todo compress
    vec_t: Vec<F>,              //<G1 as Group>::Scalar>,
    decommit_doc: F,            //<G1 as Group>::Scalar,
    pub commit_doc_hash: F,     //<G1 as Group>::Scalar,
}
/*
impl DocCommitmentStruct {
    pub fn get_commit_coord(&self) -> Vec<<G1 as Group>::Scalar> {
        let coordinates = self.commit_doc.to_coordinates();

        vec![coordinates.0, coordinates.1]
    }
} TODO*/

pub fn gen_commitment(
    commit_docype: JCommit,
    doc: Vec<usize>,
    pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
) -> ReefCommitment<<G1 as Group>::Scalar>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
{
    type F = <G1 as Group>::Scalar;
    match commit_docype {
        JCommit::HashChain => {
            let mut hash;

            // H_0 = Hash(0, r, 0)
            let mut sponge = Sponge::new_with_constants(pc, Mode::Simplex);
            let acc = &mut ();

            let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
            sponge.start(parameter, None, acc);

            let blind = <G1 as Group>::Scalar::random(&mut OsRng);

            // println!("HASH BLIND: {:#?}", blind.clone());

            SpongeAPI::absorb(&mut sponge, 2, &[blind, F::from(0)], acc);
            hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();

            // println!("RANDOM HASH: {:#?}", hash[0].clone());

            let mut i = 0;
            // H_i = Hash(H_i-1, char, i)
            for c in doc.into_iter() {
                let mut sponge = Sponge::new_with_constants(pc, Mode::Simplex);
                let acc = &mut ();

                let parameter = IOPattern(vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
                sponge.start(parameter, None, acc);

                // println!(
                //     "REAL HASH ELTS: {:#?}, {:#?}, {:#?}",
                //     hash[0],
                //     F::from(c as u64),
                //     F::from(i)
                // );

                SpongeAPI::absorb(
                    &mut sponge,
                    3,
                    &[hash[0], F::from(c as u64), F::from(i)],
                    acc,
                );
                hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
                sponge.finish(acc).unwrap();
                i += 1;
            }
            // println!("commitment = {:#?}", hash.clone());
            //self.hash_commitment = Some((start, hash[0]));

            return ReefCommitment::HashChain(HashCommitmentStruct {
                commit: hash[0],
                blind: blind,
            });
        }
        JCommit::Nlookup => {
            let doc_ext_len = doc.len().next_power_of_two();

            let mut doc_ext: Vec<Integer> = doc.into_iter().map(|x| Integer::from(x)).collect();
            doc_ext.append(&mut vec![Integer::from(0); doc_ext_len - doc_ext.len()]);

            let mle = mle_from_pts(doc_ext);
            // println!("mle: {:#?}", mle);

            let gens_t = CommitmentGens::<G1>::new(b"nlookup document commitment", mle.len()); // n is dimension
            let blind = F::random(&mut OsRng);

            let scalars: Vec<F> = //<G1 as Group>::Scalar> =
                mle.into_iter().map(|x| int_to_ff(x)).collect();

            let commit_doc = <G1 as Group>::CE::commit(&gens_t, &scalars, &blind);
            // TODO compress ?
            //self.doc_commitement = Some(commitment);

            // for in circuit hashing
            let mut ro: PoseidonRO<<G2 as Group>::Scalar, F> =
                PoseidonRO::new(PoseidonConstantsCircuit::new(), 3);
            commit_doc.absorb_in_ro(&mut ro);
            let commit_doc_hash = ro.squeeze(128);

            let doc_commit = DocCommitmentStruct {
                gens: gens_t.clone(),
                gens_single: CommitmentGens::<G1>::new_with_blinding_gen(
                    b"gens_s",
                    1,
                    &gens_t.get_blinding_gen(),
                ),
                commit_doc: commit_doc,
                vec_t: scalars,
                decommit_doc: blind,
                commit_doc_hash: commit_doc_hash,
            };

            return ReefCommitment::Nlookup(doc_commit);
        }
    }
}

// this crap will need to be seperated out
pub fn proof_dot_prod(
    dc: DocCommitmentStruct<<G1 as Group>::Scalar>,
    running_q: Vec<<G1 as Group>::Scalar>,
    running_v: <G1 as Group>::Scalar,
) -> Result<(), NovaError> {
    let mut p_transcript = Transcript::new(b"dot_prod_proof");
    let mut v_transcript = Transcript::new(b"dot_prod_proof");

    // set up
    let decommit_running_v = <G1 as Group>::Scalar::random(&mut OsRng);
    let commit_running_v =
        <G1 as Group>::CE::commit(&dc.gens_single, &[running_v.clone()], &decommit_running_v);

    // prove
    let ipi: InnerProductInstance<G1> =
        InnerProductInstance::new(&dc.commit_doc, &running_q, &commit_running_v);
    let ipw =
        InnerProductWitness::new(&dc.vec_t, &dc.decommit_doc, &running_v, &decommit_running_v);
    let ipa =
        InnerProductArgument::prove(&dc.gens, &dc.gens_single, &ipi, &ipw, &mut p_transcript)?;

    // verify
    let num_vars = running_q.len();
    ipa.verify(&dc.gens, &dc.gens_single, num_vars, &ipi, &mut v_transcript)?;

    Ok(())
}

pub fn final_clear_checks(
    eval_type: JBatching,
    reef_commitment: ReefCommitment<<G1 as Group>::Scalar>,
    accepting_state: <G1 as Group>::Scalar,
    table: &Vec<Integer>,
    doc_len: usize,
    final_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_v: Option<<G1 as Group>::Scalar>,
    final_hash: Option<<G1 as Group>::Scalar>,
    final_doc_q: Option<Vec<<G1 as Group>::Scalar>>,
    final_doc_v: Option<<G1 as Group>::Scalar>,
) {
    // state matches?
    assert_eq!(accepting_state, <G1 as Group>::Scalar::from(1));

    // nlookup eval T check
    match (final_q, final_v) {
        (Some(q), Some(v)) => {
            // T is in the clear for this case
            match eval_type {
                JBatching::NaivePolys => {
                    panic!(
                        "naive poly evaluation used, but running claim provided for verification"
                    );
                }
                JBatching::Nlookup => {
                    let mut q_i = vec![];
                    for f in q {
                        q_i.push(Integer::from_digits(f.to_repr().as_ref(), Order::Lsf));
                    }
                    // TODO mle eval over F
                    assert_eq!(
                        verifier_mle_eval(table, &q_i),
                        (Integer::from_digits(v.to_repr().as_ref(), Order::Lsf))
                    );
                }
            }
        }
        (Some(_), None) => {
            panic!("only half of running claim recieved");
        }
        (None, Some(_)) => {
            panic!("only half of running claim recieved");
        }
        (None, None) => {
            if matches!(eval_type, JBatching::Nlookup) {
                panic!("nlookup evaluation used, but no running claim provided for verification");
            }
        }
    }

    // todo vals align
    // hash chain commitment check
    match reef_commitment {
        ReefCommitment::HashChain(h) => {
            // todo substring
            assert_eq!(h.commit, final_hash.unwrap());
        }
        ReefCommitment::Nlookup(dc) => {
            // or - nlookup commitment check
            match (final_doc_q, final_doc_v) {
                (Some(q), Some(v)) => {
                    /*println!(
                        "final doc check fixing q,v: {:#?}, {:#?}, dc: {:#?}",
                        q, v, dc
                    );*/

                    let doc_ext_len = doc_len.next_power_of_two();

                    // right form for inner product
                    let q_rev = q.clone().into_iter().rev().collect(); // todo get rid clone
                    let q_ext = q_to_mle_q(&q_rev, doc_ext_len);

                    // Doc is commited to in this case
                    assert!(proof_dot_prod(dc, q_ext, v).is_ok());
                }
                (Some(_), None) => {
                    panic!("only half of running claim recieved");
                }
                (None, Some(_)) => {
                    panic!("only half of running claim recieved");
                }
                (None, None) => {
                    panic!(
                    "nlookup doc commitment used, but no running claim provided for verification"
                );
                }
            }
        }
    }

    println!("Final values confirmed in the clear!");
}

// TODO test, TODO over ff, not Integers
// calculate multilinear extension from evals of univariate
// must "pad out" pts to power of 2 !
fn mle_from_pts(pts: Vec<Integer>) -> Vec<Integer> {
    //println!("mle pts {:#?}", pts);

    let num_pts = pts.len();
    if num_pts == 1 {
        return vec![pts[0].clone()];
    }

    let h = num_pts / 2;
    // println!("num_pts {}, h {}", num_pts, h);

    let mut l = mle_from_pts(pts[..h].to_vec());
    let mut r = mle_from_pts(pts[h..].to_vec());

    for i in 0..r.len() {
        r[i] -= &l[i];
        l.push(r[i].clone().rem_floor(cfg().field().modulus()));
    }

    l
}

fn q_to_mle_q(q: &Vec<<G1 as Group>::Scalar>, mle_len: usize) -> Vec<<G1 as Group>::Scalar> {
    let mut q_out = vec![];
    let base: usize = 2;

    for idx in 0..mle_len {
        let mut new_term = <G1 as Group>::Scalar::from(1);
        for j in 0..q.len() {
            // for each possible var in this term
            if (idx / base.pow(j as u32)) % 2 == 1 {
                // is this var in this term?
                new_term *= q[j].clone(); // todo?
                                          //println!("new term after mul {:#?}", new_term);
                                          // note this loop is never triggered for constant :)
            }
        }

        q_out.push(new_term); //.rem_floor(cfg().field().modulus()));
    }

    q_out
}

#[cfg(test)]
mod tests {

    use crate::backend::commitment::*;
    use crate::backend::nova::int_to_ff;
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
        let mut sum = <G1 as Group>::Scalar::from(0);
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

        // println!("ipa {:#?}", ipa.clone().unwrap());
        let res = ipa
            .unwrap()
            .verify(&gens_t, &gens_single, num_vars, &ipi, &mut v_transcript);
        // println!("res {:#?}", res);

        // this doesn't pass
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
        // println!("mle coeffs: {:#?}", mle);

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

        // println!("q_ext: {:#?}", q_ext);

        assert_eq!(mle_f.len(), q_ext.len());
        // inner product
        let mut sum = <G1 as Group>::Scalar::from(0);
        for i in 0..mle.len() {
            sum += mle_f[i].clone() * q_ext[i].clone();
        }
        assert_eq!(sum, <G1 as Group>::Scalar::from(1162));
    }
}
