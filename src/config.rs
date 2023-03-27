use clap::{Parser, Subcommand, ValueEnum};
use std::collections::HashSet;
use std::fmt::Debug;
use std::fs::File;
use std::io::{BufReader, Read};
use std::marker::PhantomData;
use std::path::PathBuf;

use crate::backend::costs::{JBatching, JCommit};
use crate::dfa::DFA;
use crate::regex::Regex;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
pub struct Options {
    /// Configuration options, charset ["ascii", "utf8", "dna"]
    #[command(subcommand)]
    pub config: Config,
    #[arg(
        short = 'e',
        long = "eval-type",
        value_name = "EVAL TYPE",
        help = "naive-polys or nlookup evals (override auto select)"
    )]
    pub eval_type: Option<JBatching>,
    #[arg(
        short = 'c',
        long = "commit-type",
        value_name = "COMMIT TYPE",
        help = "hash-chain or nlookup commitment (override auto select)"
    )]
    pub commit_type: Option<JCommit>,
    #[arg(
        short = 'b',
        long = "batch-size",
        value_name = "USIZE",
        help = "Batch size (override auto select)",
        default_value_t = 0, // auto select
    )]
    pub batch_size: usize,
}

#[derive(Debug, Subcommand)]
pub enum Config {
    #[clap(about = "Accepts ASCII regular-expressions and documents")]
    Ascii {
        #[arg(
            short = 't',
            long = "transforms",
            value_delimiter = ',',
            help = "Transformations to apply to the input, in order"
        )]
        trs: Vec<CharTransform>,
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf,
    },
    #[clap(about = "Accepts UTF8 regular-expressions and documents")]
    Utf8 {
        #[arg(
            short = 't',
            long = "transforms",
            value_delimiter = ',',
            help = "Transformations to apply to the input, in order"
        )]
        trs: Vec<CharTransform>,
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf,
    },
    #[clap(about = "Accepts .pcap files and Snort rules")]
    Snort {
        #[arg(
            short = 'r',
            long = "rules",
            value_name = "FILE",
            help = "Snort rule file"
        )]
        rulesfile: PathBuf,
        #[arg(short = 'i', long = "input", value_name = "FILE", help = "Pcap file")]
        pcapfile: PathBuf,
    },
    #[clap(about = "Accepts DNA base ASCII files")]
    Dna {
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf,
    },
    #[clap(
        about = "Infer the smallest alphabet that works from the regular expression and document"
    )]
    Auto {
        #[arg(short = 'r', long)]
        re: String,
        #[arg(short = 'i', long, value_name = "FILE")]
        inp: PathBuf,
    },
}

#[derive(Debug, Clone, ValueEnum)]
pub enum CharTransform {
    AlphaNumeric,
    BasicEnglish,
    IgnoreWhitespace,
    CaseInsensitive,
}

/// Top level
impl Config {
    pub fn read_doc(&self) -> Vec<char> {
        match self {
            Config::Ascii { inp, .. } => self.read_file(inp),
            Config::Utf8 { inp, .. } => self.read_file(inp),
            Config::Dna { inp, .. } => self.read_file(inp),
            Config::Auto { inp, .. } => self.read_file(inp),
            Config::Snort { .. } => Vec::new(), // TODO
        }
    }

    pub fn compile_dfa(&self) -> DFA {
        let ab = String::from_iter(self.alphabet());
        let re = match self {
            Config::Ascii { re, .. } => Regex::new(re),
            Config::Utf8 { re, .. } => Regex::new(re),
            Config::Dna { re, .. } => Regex::new(re),
            Config::Auto { re, .. } => Regex::new(re),
            Config::Snort { .. } => Regex::empty(), // TODO
        };
        DFA::new(&ab, re)
    }
}

/// Define how to encode a Datatype
pub trait Encoder<I, F> {
    fn alphabet(&self, s: &Vec<I>) -> Vec<F>;
    fn apply(&self, s: I) -> Option<F>;
    fn priority(&self) -> usize;
    fn get_alphabet(&self) -> Vec<F> {
        self.alphabet(&Vec::new())
    }
}

/// How to read an input file
pub trait BaseParser<F> {
    fn alphabet(&self) -> Vec<F>;
    fn read_file(&self, file: &PathBuf) -> Vec<F>;
}

/// Encoders are compositional like functions
struct Compose<'a, A, B, C, F, G>
where
    F: Encoder<A, B>,
    G: Encoder<B, C>,
{
    f: &'a F,
    g: &'a G,
    // Rust compiler is both stupid and strict here
    ghost_a: PhantomData<A>,
    ghost_b: PhantomData<B>,
    ghost_c: PhantomData<C>,
}

/// BaseParsers can be composed with encoders
struct ComposeBase<'a, A, B, F, G>
where
    F: BaseParser<A>,
    G: Encoder<A, B>,
{
    f: &'a F,
    g: &'a G,
    ghost_a: PhantomData<A>,
    ghost_b: PhantomData<B>,
}

/// Compose encoders (ctor)
impl<'a, A, B, C, F, G> Compose<'a, A, B, C, F, G>
where
    F: Encoder<A, B>,
    G: Encoder<B, C>,
{
    fn new(f: &'a F, g: &'a G) -> Self {
        Self {
            f,
            g,
            ghost_a: PhantomData,
            ghost_b: PhantomData,
            ghost_c: PhantomData,
        }
    }
}

/// Compose encoders (semantics)
impl<'a, A, B, C, F: Encoder<A, B>, G: Encoder<B, C>> Encoder<A, C> for Compose<'a, A, B, C, F, G> {
    fn alphabet(&self, s: &Vec<A>) -> Vec<C> {
        self.g.alphabet(&self.f.alphabet(s))
    }
    fn priority(&self) -> usize {
        self.f.priority().max(self.g.priority())
    }
    fn apply(&self, s: A) -> Option<C> {
        self.f.apply(s).and_then(|c| self.g.apply(c))
    }
}

/// Compose base parsers + encoders (ctor)
impl<'a, A, B, F, G> ComposeBase<'a, A, B, F, G>
where
    F: BaseParser<A>,
    G: Encoder<A, B>,
{
    fn new(f: &'a F, g: &'a G) -> Self {
        Self {
            f,
            g,
            ghost_a: PhantomData,
            ghost_b: PhantomData,
        }
    }
}

/// Compose base parsers + encoders (semantics)
impl<'a, A, B, F: BaseParser<A>, G: Encoder<A, B>> BaseParser<B> for ComposeBase<'a, A, B, F, G> {
    fn alphabet(&self) -> Vec<B> {
        self.g.alphabet(&self.f.alphabet())
    }
    fn read_file(&self, file: &PathBuf) -> Vec<B> {
        self.f
            .read_file(file)
            .into_iter()
            .filter_map(|c| self.g.apply(c))
            .collect()
    }
}

/// Parser for ASCII files
struct AsciiParser;
impl BaseParser<char> for AsciiParser {
    fn alphabet(&self) -> Vec<char> {
        (0..128).filter_map(std::char::from_u32).collect()
    }
    fn read_file(&self, file: &PathBuf) -> Vec<char> {
        let f = File::open(file).expect("Could not read document");
        let mut reader = BufReader::new(f);
        let mut buffer: Vec<u8> = Vec::new();
        // Read file into vector.
        reader.read_to_end(&mut buffer);
        buffer.into_iter().map(|i| i as char).collect()
    }
}

/// Parser for UTF8 files
struct Utf8Parser;
impl BaseParser<char> for Utf8Parser {
    fn alphabet(&self) -> Vec<char> {
        (0..=0x10FFFF).filter_map(std::char::from_u32).collect()
    }
    fn read_file(&self, file: &PathBuf) -> Vec<char> {
        std::fs::read_to_string(file)
            .expect("file not found!")
            .chars()
            .collect()
    }
}

/// Read Ascii encoded DNA bases
struct DnaParser;
impl BaseParser<char> for DnaParser {
    fn alphabet(&self) -> Vec<char> {
        vec!['A', 'C', 'G', 'T']
    }
    fn read_file(&self, file: &PathBuf) -> Vec<char> {
        let doc = AsciiParser.read_file(file);
        for c in doc.iter() {
            assert!(
                self.alphabet().contains(&c),
                "{} not in the alphabet {:?}",
                c,
                self.alphabet()
            );
        }
        doc
    }
}

/// Automatically infer the alphabet from the alphanumeric chars of the regex
struct AutoParser {
    ab: Vec<char>,
}
impl AutoParser {
    fn new(inp: &PathBuf, re: &String) -> Self {
        let docab = std::fs::read_to_string(inp)
            .expect("Could not read document")
            .trim()
            .chars()
            .collect::<HashSet<char>>();

        let reab = re
            .chars()
            .filter(|c| c.is_alphanumeric())
            .collect::<HashSet<char>>();

        Self {
            ab: docab.union(&reab).map(|c| c.clone()).collect(),
        }
    }
}

impl BaseParser<char> for AutoParser {
    fn alphabet(&self) -> Vec<char> {
        self.ab.clone()
    }
    fn read_file(&self, file: &PathBuf) -> Vec<char> {
        let doc = Utf8Parser.read_file(file);
        for c in doc.iter() {
            assert!(
                self.ab.contains(&c),
                "{} not in the alphabet {:?}",
                c,
                self.ab
            );
        }
        doc
    }
}

////////////////////////////////////////////////////////////
////////////////////// TRANSFORMATIONS /////////////////////
////////////////////////////////////////////////////////////

/// Only accept alphanumeric ASCII and UTF8
struct AlphaNumericEncoder;
impl Encoder<char, char> for AlphaNumericEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        let lower = 'a'..='z';
        let upper = 'A'..='Z';
        let numbers = '0'..='9';
        lower
            .into_iter()
            .chain(upper.into_iter())
            .chain(numbers.into_iter())
            .collect()
    }
    fn priority(&self) -> usize {
        99999
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
impl Encoder<char, char> for IgnoreWhitespaceEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        s.clone()
            .into_iter()
            .filter(|c| !c.is_whitespace())
            .collect()
    }
    fn priority(&self) -> usize {
        100
    }
    fn apply(&self, s: char) -> Option<char> {
        if s.is_whitespace() {
            None
        } else {
            Some(s)
        }
    }
}

/// Make all characters uppercase (ASCII)
struct CaseInsensitiveEncoder;
impl Encoder<char, char> for CaseInsensitiveEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        s.clone()
            .into_iter()
            .filter(|c| !c.is_ascii_lowercase())
            .collect()
    }
    fn priority(&self) -> usize {
        200
    }
    fn apply(&self, s: char) -> Option<char> {
        Some(s.to_ascii_uppercase())
    }
}

/// Basic english alphabet + symbols [,.!?;:-'$&*+@"]
struct BasicEnglishEncoder;
impl Encoder<char, char> for BasicEnglishEncoder {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        let lower = 'a'..='z';
        let upper = 'A'..='Z';
        let numbers = '0'..='9';
        let mut whitespace = vec![' ', '\n'];
        let mut symbols = vec![
            ',', '.', '!', '?', ';', ':', '-', '\'', '"', '$', '&', '*', '+', '@',
        ];
        let mut v: Vec<char> = (lower.chain(upper).chain(numbers)).collect();
        v.append(&mut symbols);
        v.append(&mut whitespace);
        v
    }
    fn priority(&self) -> usize {
        999999
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
impl Encoder<char, char> for &CharTransform {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        match self {
            CharTransform::AlphaNumeric => AlphaNumericEncoder.alphabet(s),
            CharTransform::IgnoreWhitespace => IgnoreWhitespaceEncoder.alphabet(s),
            CharTransform::CaseInsensitive => CaseInsensitiveEncoder.alphabet(s),
            CharTransform::BasicEnglish => BasicEnglishEncoder.alphabet(s),
        }
    }
    fn priority(&self) -> usize {
        match self {
            CharTransform::AlphaNumeric => AlphaNumericEncoder.priority(),
            CharTransform::IgnoreWhitespace => IgnoreWhitespaceEncoder.priority(),
            CharTransform::CaseInsensitive => CaseInsensitiveEncoder.priority(),
            CharTransform::BasicEnglish => BasicEnglishEncoder.priority(),
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

impl Encoder<char, char> for &Vec<CharTransform> {
    fn alphabet(&self, s: &Vec<char>) -> Vec<char> {
        self.iter().fold(s.clone(), |acc, enc| enc.alphabet(&acc))
    }
    fn priority(&self) -> usize {
        self.iter().fold(0, |acc, enc| enc.priority().max(acc))
    }
    fn apply(&self, s: char) -> Option<char> {
        self.iter()
            .fold(Some(s), |acc, enc| acc.and_then(|c| enc.apply(c)))
    }
}

/// One more disjoint union, Config is an encoder
impl BaseParser<char> for Config {
    fn alphabet(&self) -> Vec<char> {
        match self {
            Config::Ascii { trs, .. } => ComposeBase::new(&AsciiParser, &trs).alphabet(),
            Config::Utf8 { trs, .. } => ComposeBase::new(&Utf8Parser, &trs).alphabet(),
            Config::Dna { .. } => DnaParser.alphabet(),
            Config::Auto { re, inp, .. } => AutoParser::new(inp, re).alphabet(),
            Config::Snort { .. } => Vec::new(), // TODO
        }
    }

    fn read_file(&self, file: &PathBuf) -> Vec<char> {
        match self {
            Config::Ascii { trs, .. } => ComposeBase::new(&AsciiParser, &trs).read_file(file),
            Config::Utf8 { trs, .. } => ComposeBase::new(&Utf8Parser, &trs).read_file(file),
            Config::Dna { .. } => DnaParser.read_file(file),
            Config::Auto { re, inp, .. } => AutoParser::new(inp, re).read_file(file),
            Config::Snort { .. } => Vec::new(), // TODO
        }
    }
}