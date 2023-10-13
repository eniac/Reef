type G1 = pasta_curves::pallas::Point;

use ff::{Field, PrimeField};
use generic_array::typenum;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
};
use nova_snark::traits::Group;

#[derive(Debug, Clone)]
pub struct MerkleCommitment<F: PrimeField> {
    pub commitment: F,
    tree: Vec<Vec<F>>,
    doc: Vec<F>,
}

#[derive(Debug, Clone)]
pub struct MerkleWit<F: PrimeField> {
    pub l_or_r: bool,
    pub opposite_idx: Option<F>,
    pub opposite: F,
}

impl<F: PrimeField> MerkleCommitment<F> {
    pub fn new(doc: &Vec<usize>, pc: &PoseidonConstants<F, typenum::U4>) -> Self {
        let mut tree = vec![];
        let mut doc_f = vec![];

        // leafs
        let mut i = 0;
        let mut next_level = vec![];
        while i < doc.len() {
            let char_i = F::from(doc[i] as u64);
            doc_f.push(char_i);
            let left = (Some(F::from(i as u64)), char_i);

            let right = if i + 1 < doc.len() {
                let char_ip = F::from(doc[i + 1] as u64);
                doc_f.push(char_ip);
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

    pub fn make_wits(&self, m_lookups: &Vec<usize>) -> Vec<Vec<MerkleWit<F>>> {
        let mut wits = vec![];

        for q in m_lookups {
            let tree_wits = self.path_wits(*q);

            wits.push(tree_wits);
        }

        wits
    }

    pub fn path_wits(&self, idx: usize) -> Vec<MerkleWit<F>> {
        assert!(idx < self.doc.len());
        let mut sel_wit = vec![]; // (l_or_r, opposite F)

        let wit = match idx % 2 {
            0 => {
                if idx + 1 >= self.doc.len() {
                    // TODO potentially make the "padding"
                    // something else

                    MerkleWit {
                        l_or_r: true,
                        opposite_idx: Some(F::zero()),
                        opposite: F::zero(),
                    }
                } else {
                    MerkleWit {
                        l_or_r: true,
                        opposite_idx: Some(F::from((idx + 1) as u64)),
                        opposite: self.doc[idx + 1],
                    }
                }
            }
            1 => MerkleWit {
                l_or_r: false,
                opposite_idx: Some(F::from((idx - 1) as u64)),
                opposite: self.doc[idx - 1],
            },
            _ => {
                panic!("bad % 2");
            }
        };
        sel_wit.push(wit);

        let mut quo = idx / 2;
        for h in 0..(self.tree.len() - 1) {
            let wit = match quo % 2 {
                0 => {
                    if quo + 1 >= self.tree[h].len() {
                        MerkleWit {
                            l_or_r: true,
                            opposite_idx: None,
                            opposite: F::zero(),
                        }
                    } else {
                        MerkleWit {
                            l_or_r: true,
                            opposite_idx: None,
                            opposite: self.tree[h][quo + 1],
                        }
                    }
                }
                1 => MerkleWit {
                    l_or_r: false,
                    opposite_idx: None,
                    opposite: self.tree[h][quo - 1],
                },
                _ => {
                    panic!("bad % 2");
                }
            };
            sel_wit.push(wit);
            quo = quo / 2;
        }

        sel_wit
    }
}

#[cfg(test)]
mod tests {

    type G1 = pasta_curves::pallas::Point;
    use crate::backend::merkle_tree::MerkleCommitment;
    use generic_array::typenum;
    use neptune::poseidon::PoseidonConstants;
    use neptune::sponge::api::IOPattern;
    use neptune::sponge::api::SpongeAPI;
    use neptune::sponge::api::SpongeOp;
    use neptune::sponge::vanilla::Mode;
    use neptune::sponge::vanilla::{Sponge, SpongeTrait};
    use neptune::Strength;
    use nova_snark::traits::Group;

    #[test]
    fn make_mt() {
        let pc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);
        // "document"
        let doc = vec![2, 3, 4, 5, 6, 7, 8];

        let mc = MerkleCommitment::new(&doc, &pc);

        let qs = vec![0, 1, 2, 3, 4, 5, 6];
        let tree_wits = mc.make_wits(&qs);

        for i in 0..qs.len() {
            // leafs
            let w0 = tree_wits[i][0].opposite_idx.unwrap();
            let w1 = tree_wits[i][0].opposite;

            let mut query = vec![];
            if tree_wits[i][0].l_or_r {
                query.push(<G1 as Group>::Scalar::from(qs[i] as u64));
                query.push(<G1 as Group>::Scalar::from(doc[qs[i]] as u64));
                query.push(w0);
                query.push(w1);
            } else {
                query.push(w0);
                query.push(w1);
                query.push(<G1 as Group>::Scalar::from(qs[i] as u64));
                query.push(<G1 as Group>::Scalar::from(doc[qs[i]] as u64));
            }

            let mut hash = hash_children(&query, &pc);

            for h in 1..tree_wits[i].len() {
                let w = tree_wits[i][h].opposite;

                let mut query = vec![];
                if tree_wits[i][h].l_or_r {
                    query.push(hash);
                    query.push(w);
                } else {
                    query.push(w);
                    query.push(hash);
                }

                hash = hash_children(&query, &pc);
            }

            assert_eq!(hash, mc.commitment);
        }
    }

    fn hash_children(
        query: &[<G1 as Group>::Scalar],
        pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
    ) -> <G1 as Group>::Scalar {
        let mut sponge = Sponge::new_with_constants(pc, Mode::Simplex);
        let acc = &mut ();

        let parameter = IOPattern(vec![
            SpongeOp::Absorb(query.len() as u32),
            SpongeOp::Squeeze(1),
        ]);
        sponge.start(parameter, None, acc);

        SpongeAPI::absorb(&mut sponge, query.len() as u32, query, acc);
        let out = SpongeAPI::squeeze(&mut sponge, 1, acc);
        sponge.finish(acc).unwrap();

        out[0]
    }
}
