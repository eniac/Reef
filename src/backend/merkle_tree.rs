type G1 = pasta_curves::pallas::Point;
type F = <G1 as Group>::Scalar;

use ff::{Field, PrimeField};
use generic_array::typenum;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
};
use nova_snark::traits::Group;

#[derive(Debug, Clone)]
pub struct MerkleCommitment {
    commitment: F,
    tree: Vec<Vec<F>>,
    pc: PoseidonConstants<F, typenum::U4>,
}

impl MerkleCommitment {
    pub fn new(doc: Vec<usize>, pc: &PoseidonConstants<F, typenum::U4>) -> Self {
        let mut tree = vec![];

        // leafs
        let mut i = 0;
        let mut next_level = vec![];
        while i < doc.len() {
            let left = (Some(F::from(i as u64)), F::from(doc[i] as u64));
            let right = if i + 1 < doc.len() {
                Some((Some(F::from((i + 1) as u64)), F::from(doc[i + 1] as u64)))
            } else {
                None
            };

            let p = Self::new_parent(left, right, pc);
            next_level.push(p);

            i += 2;
        }
        tree.push(next_level.clone());

        // non leafs
        while next_level.len() > 1 {
            i = 0;
            let prev = next_level;
            next_level = vec![];
            while i < prev.len() {
                let left = (None, prev[i]);
                let right = if i + 1 < prev.len() {
                    Some((None, prev[i + 1]))
                } else {
                    None
                };

                let p = Self::new_parent(left, right, pc);
                next_level.push(p);

                i += 2;
            }
            tree.push(next_level.clone());
        }

        Self {
            commitment: next_level[0],
            tree,
            pc: pc.clone(),
        }
    }

    fn new_parent(
        left: (Option<F>, F),
        right: Option<(Option<F>, F)>, // idx, c
        pc: &PoseidonConstants<F, typenum::U4>,
    ) -> F {
        let mut sponge = Sponge::new_with_constants(pc, Mode::Simplex);
        let acc = &mut ();

        let query = match (left, right) {
            ((Some(li), lc), Some((Some(ri), rc))) => {
                vec![li, lc, ri, rc]
            }
            ((Some(li), lc), None) => {
                vec![li, lc, F::zero(), F::zero()]
            }
            ((None, lc), Some((None, rc))) => {
                vec![lc, rc]
            }
            ((None, lc), None) => {
                vec![lc, F::zero()]
            }
            _ => {
                panic!("not a correctly formatted leaf or parent");
            }
        };

        let absorb = query.len() as u32;
        let parameter = IOPattern(vec![SpongeOp::Absorb(absorb), SpongeOp::Squeeze(1)]);
        sponge.start(parameter, None, acc);
        SpongeAPI::absorb(&mut sponge, absorb, &query, acc);
        let hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
        sponge.finish(acc).unwrap();

        hash[0]
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn commit() {}
}
