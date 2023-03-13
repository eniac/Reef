use std::fs::File;
use std::io::{BufReader, Read};
use bitvec::prelude::*;
use clap::{Parser, Subcommand, ValueEnum};
use std::fmt::Debug;
use std::path::PathBuf;
use std::collections::HashSet;
use std::marker::PhantomData;

use crate::parser::{regex_parser, re :: *};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
pub struct Options {
    /// Configuration options, charset ["ascii", "utf8", "dna"]
    #[command(subcommand)]
    pub config: Config,
}

#[derive(Debug, Subcommand)]
pub enum Config {
    #[clap(about = "Accepts ASCII regular-expressions and documents")]
    Ascii {
        #[arg(short = 't', long = "transforms", value_delimiter=',', help = "Transformations to apply to the input, in order")]
        trs: Vec<CharTransform>,
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf,
    },
    #[clap(about = "Accepts UTF8 regular-expressions and documents")]
    Utf8 {
        #[arg(short = 't', long = "transforms", value_delimiter=',', help = "Transformations to apply to the input, in order")]
        trs: Vec<CharTransform>,
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf,
    },
    #[clap(about = "Accepts DNA base encoded binary files (2-bits/base)")]
    Dna {
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf,
    },
    #[clap(about = "Infer the smallest alphabet that works from the regular expression and document")]
    Auto {
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf
    }
}

#[derive(Debug, Clone, ValueEnum)]
pub enum CharTransform {
    AlphaNumeric,
    BasicEnglish,
    IgnoreWhitespace,
    CaseInsensitive
}

impl Config {
    // Number of bits in each segment
    fn nbits(&self) -> usize {
        match self {
            Config::Ascii { .. } => 8,
            Config::Utf8 { .. } => 32,
            Config::Dna { .. } => 2,
            Config::Auto { .. } => 8
        }
    }

    fn filename(&self) -> &PathBuf {
        match self {
            Config::Ascii { inp, .. } => inp,
            Config::Utf8 { inp, .. } => inp,
            Config::Dna { inp, .. } => inp,
            Config::Auto { inp, .. } => inp
        }
    }
}

pub fn parse_regex(conf: &Config) -> Regex {
        let ab = String::from_iter(conf.get_alphabet());
        match conf {
            Config::Ascii { re, .. } => regex_parser(re, &ab),
            Config::Utf8 { re, .. } => regex_parser(re, &ab),
            Config::Dna { re, .. } => regex_parser(re, &ab),
            Config::Auto { re, .. } => regex_parser(re, &ab),
        }
}


// #[clap(value_enum, default_value_t=CharTransform::NoTransform)]
/// Define how to encode a Datatype
/// preserves length.
pub trait Encoder<I, F> {
    fn alphabet(&self, s: &Vec<I>) -> Vec<F>;
    fn apply(&self, s: I) -> Option<F>;
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
    fn apply(&self, s: A) -> Option<C> {
        self.f.apply(s).and_then(|c| self.g.apply(c))
    }
}

/// Encoder for ascii char
struct AsciiEncoder;
impl Encoder<u32,char> for AsciiEncoder {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
        (0..127)
            .filter_map(std::char::from_u32)
            .collect()
    }

    fn apply(&self, s: u32) -> Option<char> {
        std::char::from_u32(s)
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
    fn apply(&self, s: u32) -> Option<char> {
        std::char::from_u32(s)
    }
}

/// Take two bits into DNA bases
struct DnaEncoder;
impl Encoder<u32,char> for DnaEncoder {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
        vec!['A', 'C', 'G', 'T']
    }
    fn apply(&self, s: u32) -> Option<char> {
        self.get_alphabet().get(s as usize).map(|c| c.clone())
    }
}

/// Automatically infer the alphabet from the alphanumeric chars of the regex
struct AutoEncoder { ab: Vec<char> }
impl AutoEncoder {
    fn new(inp: &PathBuf, re: &String) -> Self {
        let docab = std::fs::read_to_string(inp)
            .expect("Could not read document")
            .trim()
            .chars()
            .collect::<HashSet<char>>();

        let reab =
            re.chars().filter(|c| c.is_alphanumeric())
                .collect::<HashSet<char>>();

        Self { ab : docab.union(&reab).map(|c| c.clone()).collect() }
    }
}

impl Encoder<u32,char> for AutoEncoder {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
        self.ab.clone()
    }
    fn apply(&self, s: u32) -> Option<char> {
        let ab = self.get_alphabet();
        let c = std::char::from_u32(s).unwrap();
        assert!(ab.contains(&c), "{} not in the alphabet {:?}", c, ab);
        Some(c)
    }
}


////////////////////////////////////////////////////////////
////////////////////// TRANSFORMATIONS /////////////////////
////////////////////////////////////////////////////////////

/// Only accept alphanumeric ASCII and UTF8
struct AlphaNumericEncoder;
impl Encoder<char,char> for AlphaNumericEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        let lower = 'a'..='z';
        let upper = 'A'..='Z';
        let numbers = '0'..='9';
        lower.into_iter()
            .chain(upper.into_iter())
            .chain(numbers.into_iter())
            .collect()
    }
    fn apply(&self, s: char) -> Option<char> {
        if self.get_alphabet().contains(&s) {
            Some(s)
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
         .collect()
    }
    fn apply(&self, s: char) -> Option<char> {
        if s.is_whitespace() { None } else { Some(s) }
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
    fn apply(&self, s: char) -> Option<char> {
        Some(s.to_ascii_uppercase())
    }
}

/// Basic english alphabet + symbols [,.!?;:-'$&*+@"]
struct BasicEnglishEncoder;
impl Encoder<char,char> for BasicEnglishEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
      let lower = 'a'..='z';
      let upper = 'A'..='Z';
      let numbers = '0'..='9';
      let mut whitespace = vec![' ','\n'];
      let mut symbols = vec![',','.','!','?',';',':','-','\'','"','$','&','*','+','@'];
      let mut v: Vec<char> = (lower.chain(upper).chain(numbers)).collect();
      v.append(&mut symbols);
      v.append(&mut whitespace);
      v
    }

    fn apply(&self, s: char) -> Option<char> {
        if self.get_alphabet().contains(&s) {
            Some(s)
        } else {
            panic!("Symbol {:?} is not in the basic english alphabet", s)
        }
    }
}

/// The disjoint union of encoders defined for transforms above
impl Encoder<char,char> for &CharTransform {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        match self {
            CharTransform::AlphaNumeric => AlphaNumericEncoder.get_alphabet(),
            CharTransform::IgnoreWhitespace => IgnoreWhitespaceEncoder.alphabet(s),
            CharTransform::CaseInsensitive => CaseInsensitiveEncoder.alphabet(s),
            CharTransform::BasicEnglish => BasicEnglishEncoder.alphabet(s),
        }
    }
    fn apply(&self, s: char) -> Option<char> {
        match self {
            CharTransform::AlphaNumeric => AlphaNumericEncoder.apply(s),
            CharTransform::IgnoreWhitespace => IgnoreWhitespaceEncoder.apply(s),
            CharTransform::CaseInsensitive => CaseInsensitiveEncoder.apply(s),
            CharTransform::BasicEnglish => BasicEnglishEncoder.apply(s),
        }
    }
}

impl Encoder<char,char> for &Vec<CharTransform> {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
       self.iter().fold(s.clone(), |acc, enc| enc.alphabet(&acc))
    }
    fn apply(&self, s: char) -> Option<char> {
       self.iter().fold(Some(s), |acc, enc| acc.and_then(|c| enc.apply(c)))
    }
}

/// One more disjoint union, Config is an encoder
impl Encoder<u32, char> for Config {
    fn alphabet(&self, s: &Vec<u32>) -> Vec<char> {
      match self {
          Config::Ascii { trs, .. } => Compose::new(&AsciiEncoder, &trs).get_alphabet(),
          Config::Utf8 { trs, .. } => Compose::new(&Utf8Encoder, &trs).get_alphabet(),
          Config::Dna { .. } => DnaEncoder.get_alphabet(),
          Config::Auto { re, inp, .. } => AutoEncoder::new(inp, re).get_alphabet()
      }
    }

    fn apply(&self, s: u32) -> Option<char> {
      match self {
          Config::Ascii { trs, .. } => Compose::new(&AsciiEncoder, &trs).apply(s),
          Config::Utf8 { trs, .. } => Compose::new(&Utf8Encoder, &trs).apply(s),
          Config::Dna { .. } => DnaEncoder.apply(s),
          Config::Auto { re, inp, .. } => AutoEncoder::new(inp,re).apply(s)
      }
    }
}

/// Define how to deserialize a file
pub fn read_from_config(conf: &Config) -> String {
    // Start buffering
    let filename = conf.filename();
    let file = File::open(filename).expect("Unable to open input file");
    let mut buf_reader = BufReader::new(file);
    let mut buffer = [0u8];
    let mut bit_vec = BitVec::<u8, Lsb0>::new();
    loop {
        match buf_reader.read(&mut buffer) {
            Ok(0) => break,
            Ok(_) => if buffer[0] != 0x0a {
                bit_vec.extend_from_raw_slice(&buffer)
            },
            Err(_) => panic!("Failed to read file {}.", filename.display()),
        }
    }
    String::from_iter(bit_vec.as_bitslice()
           .chunks(conf.nbits())
           .filter_map(|chunk| conf.apply(chunk.load_le::<u32>())))
}
