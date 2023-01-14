use ark_pallas::Fr;
use ark_ff::FftField;
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::poly::domain::Radix2DomainVar;

/// This object abstracts the details of padding
/// a continuous domain 0..n to a Radix2 domain
/// h*g^0, h*g^1, ..., h*g^(ceil(log2 n))
///
/// Use function [get: u64 -> Fr] to implement
/// that translation.
#[derive(Debug)]
pub struct DomainRadix2 {
    pub n: u64,
    pub lg2n: u64,
    pub inner: Radix2DomainVar<Fr>,
}

/// Ceil[log2(n)]
fn num_bits(n: u64) -> u64 {
    let mut a = 0;
    let mut e = n;
    while e > 0 {
        e = e >> 1;
        a += 1;
    }
    return a;
}

impl DomainRadix2 {
    pub fn new(size: usize) -> Self {
        let n = size as u64;
        // Upper bound number of states n = ceil[log2(dfa.nstates-1)]
        let lg2n = num_bits(n - 1);

        // Generator from root of unity
        let inner = Radix2DomainVar {
            gen: Fr::get_root_of_unity(1 << lg2n).unwrap(),
            offset: FpVar::constant(Fr::multiplicative_generator()),
            dim: lg2n,
        };

        Self { n, lg2n, inner }
    }

    /// Get the offset, or [h*g^0 = get(0)]
    pub fn get_offset(&self) -> Fr {
        self.inner.offset.value().unwrap()
    }

    /// Get the generator [g]
    pub fn get_gen(&self) -> Fr {
        self.inner.gen
    }

    /// An extension to the Radix2DomainVar to get the
    /// [i] domain value [get(i) = offset*gen^i]
    pub fn get(&self, i: u64) -> Fr {
        let mut cur = self.get_offset();
        let gen = self.get_gen();

        // We pad the domain from self.n .. 2^ceil(log2(n))
        // so for any [i] in that range, return [offset]
        if i == 0 || i >= self.n {
            cur
        } else {
            for _ in 0..i {
                cur *= gen;
            }
            cur
        }
    }

}
