use std::fs::File;
use std::io::{BufReader, Read};
use bitvec::prelude::*;
use clap::{Subcommand, Args, ValueEnum};
use std::fmt::Debug;
use std::path::PathBuf;
use std::marker::PhantomData;

#[derive(Clone, ValueEnum)]
pub enum CharTransform {
    AlphaNumeric,
    IgnoreWhitespace,
    CaseInsensitive,
    NoTransform
}

#[derive(Subcommand)]
pub enum Config {
    Ascii {
        #[clap(value_enum, default_value_t=CharTransform::NoTransform)]
        tr: CharTransform
    },
    Utf8 {
        #[clap(value_enum, default_value_t=CharTransform::NoTransform)]
        tr: CharTransform
    },
    Dna
}

/// Define how to encode a Datatype
/// preserves length.
pub trait Encoder<I, F> {
    fn alphabet(&self, s: &Vec<I>) -> Vec<F>;
    fn apply(&self, s: I) -> F;
    fn get_alphabet(&self) -> Vec<F> {
        self.alphabet(&Vec::new())
    }
}

/// Encoders are compositional like functions
struct Compose <'a, A, B, C, F, G> where F: Encoder<A,B>, G: Encoder<B,C> {
    f: &'a F, g: &'a G,
    // Rust compiler is both stupid and strict here
    ghost_a: PhantomData<A>,
    ghost_b: PhantomData<B>,
    ghost_c: PhantomData<C>
}

impl<'a, A, B, C, F, G> Compose <'a, A, B, C, F, G> where F: Encoder<A,B>, G: Encoder<B,C> {
    fn new(f: &'a F, g: &'a G) -> Self {
        Self { f, g, ghost_a: PhantomData, ghost_b: PhantomData, ghost_c: PhantomData }
    }
}

impl<'a, A, B, C, F: Encoder<A,B>, G: Encoder<B,C>> Encoder<A,C> for Compose<'a, A, B, C, F, G> {
    fn alphabet(&self, s: &Vec<A>) -> Vec<C> { self.g.alphabet(&self.f.alphabet(s)) }
    fn apply(&self, s: A) -> C {
        self.g.apply(self.f.apply(s))
    }
}

/// Encoder for ascii char
struct AsciiEncoder;
impl Encoder<u32,char> for AsciiEncoder {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
        (0u32..255u32)
            .filter_map(std::char::from_u32)
            .collect()
    }

    fn apply(&self, s: u32) -> char {
        (s as u8) as char
    }
}

/// Encoder for UTF8 char
struct Utf8Encoder;
impl Encoder<u32,char> for Utf8Encoder {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
        (0..=0x10FFFF)
            .filter_map(std::char::from_u32)
            .collect()
    }
    fn apply(&self, s: u32) -> char {
        std::char::from_u32(s)
            .expect("Not a UTF8 character")
    }
}

/// Take two bits into DNA bases
struct DnaEncoder;
impl Encoder<u32,char> for DnaEncoder {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
        vec!['A', 'C', 'G', 'T']
    }
    fn apply(&self, s: u32) -> char {
        self.get_alphabet().get(s as usize).unwrap().clone()
    }
}

////////////////////////////////////////////////////////////
////////////////////// TRANSFORMATIONS /////////////////////
////////////////////////////////////////////////////////////

/// Only accept alphanumeric ASCII and UTF8
struct AlphaNumericEncoder;
impl Encoder<char,char> for AlphaNumericEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        let lower = 'a'..'z';
        let upper = 'A'..'Z';
        let numbers = '0'..'9';
        lower.into_iter()
            .chain(upper.into_iter())
            .chain(numbers.into_iter())
            .collect()
    }
    fn apply(&self, s: char) -> char {
        if self.get_alphabet().contains(&s) {
            s
        } else {
            panic!("Symbol {} is not an alpha-numeric", s)
        }
    }
}

/// Map all different whitespaces \t, \n, \r to ' ' for ASCII and UTF8
struct IgnoreWhitespaceEncoder;
impl Encoder<char,char> for IgnoreWhitespaceEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        s.clone().into_iter()
         .filter(|c| !c.is_whitespace())
         .chain([' '].into_iter())
         .collect()
    }
    fn apply(&self, s: char) -> char {
        if s.is_whitespace() { ' ' } else { s }
    }
}

/// Make all characters uppercase (ASCII)
struct CaseInsensitiveEncoder;
impl Encoder<char,char> for CaseInsensitiveEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        s.clone().into_iter()
         .filter(|c| !c.is_ascii_lowercase())
         .collect()
    }
    fn apply(&self, s: char) -> char {
        s.to_ascii_uppercase()
    }
}

/// The disjoint union of encoders defined for transforms above
impl Encoder<char,char> for &CharTransform {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        match self {
            AlphaNumeric => AlphaNumericEncoder.get_alphabet(),
            IgnoreWhitespace => IgnoreWhitespaceEncoder.alphabet(s),
            CaseInsensitive => CaseInsensitiveEncoder.alphabet(s),
            NoTransform => s.clone()
        }
    }
    fn apply(&self, s: char) -> char {
        match self {
            AlphaNumeric => AlphaNumericEncoder.apply(s),
            IgnoreWhitespace => IgnoreWhitespaceEncoder.apply(s),
            CaseInsensitive => CaseInsensitiveEncoder.apply(s),
            NoTransform => s
        }
    }
}

/// One more disjoint union, Config is an encoder
impl Encoder<u32, char> for Config {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
      match self {
          Config::Ascii { tr } => Compose::new(&AsciiEncoder, &tr).get_alphabet(),
          Config::Utf8 { tr } => Compose::new(&Utf8Encoder, &tr).get_alphabet(),
          Config::Dna => DnaEncoder.get_alphabet()
      }
    }

    fn apply(&self, s: u32) -> char {
      match self {
          Config::Ascii { tr } => Compose::new(&AsciiEncoder, &tr).apply(s),
          Config::Utf8 { tr } => Compose::new(&Utf8Encoder, &tr).apply(s),
          Config::Dna => DnaEncoder.apply(s)
      }
    }
}

impl Config {
    // Number of bits in each segment
    fn nbits(&self) -> usize {
        match self {
            Config::Ascii { tr } => 8,
            Config::Utf8 { tr } => 32,
            Config::Dna => 2
        }
    }
}

/// Define how to deserialize a file
pub fn read_with_config(filename: &PathBuf, conf: Config) -> String {
    // Start buffering
    let file = File::open(filename).expect("Unable to open file");
    let mut buf_reader = BufReader::new(file);
    let mut buffer = [0u8, 1u8];
    let mut bit_vec = BitVec::<u8, Lsb0>::new();
    loop {
        println!("Buffer {:?}", buffer);
        match buf_reader.read(&mut buffer) {
            Ok(0) => break,
            Ok(_) => {
                let byte = buffer[0];
                bit_vec.store_le(byte);
            }
            Err(_) => panic!("Failed to read file {}.", filename.display()),
        }
    }
    String::from_iter(bit_vec.as_bitslice()
           .chunks(conf.nbits())
           .map(|chunk| conf.apply(chunk.load_le::<u32>())))
}
