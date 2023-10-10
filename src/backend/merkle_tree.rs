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
    doc: Vec<F>,
    pc: PoseidonConstants<F, typenum::U4>,
}

impl MerkleCommitment {
    pub fn new(doc: Vec<usize>, pc: &PoseidonConstants<F, typenum::U4>) -> Self {
        let mut tree = vec![];
        let mut doc_f = vec![];

        // leafs
        let mut i = 0;
        let mut next_level = vec![];
        while i < doc.len() {
            let char_i = F::from(doc[i] as u64);
            let char_ip = F::from(doc[i + 1] as u64);
            doc_f.push(char_i);
            doc_f.push(char_ip);

            let left = (Some(F::from(i as u64)), char_i);
            let right = if i + 1 < doc.len() {
                Some((Some(F::from((i + 1) as u64)), char_ip))
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
            doc: doc_f,
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

    pub fn path_wits(&self, idx: usize) -> Vec<(bool, (Option<F>, F))> {
        let sel_wit = vec![]; // (l_or_r, opposite F)

        let wit = match idx % 2 {
            0 => {
                let opposite = if idx + 1 >= self.doc.len() {
                    (Some(F::zero()), F::zero()) // TODO potentially make the "padding"
                                                 // something else
                } else {
                    (Some(F::from(idx + 1)), self.doc[idx + 1])
                };

                (true, opposite)
            }
            1 => {
                let opposite = (Some(F::from(idx - 1)), self.doc[idx - 1]);
                (false, opposite)
            }
        };
        sel_wit.push(wit);

        let mut quo = idx / 2;

        sel_wit
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn commit() {}
}
