use reef::backend::costs::*;
use reef::backend::framework::*;
use reef::backend::r1cs_helper::init;
use reef::dfa::NFA;
use reef::regex::Regex;

use csv::Writer;
use dashmap::DashMap;
use core::panic;
use std::fmt::Display;
use std::fs::File;
use std::io::{self, prelude::*};

#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub enum Component {
    Compiler,
    Prover,
    Solver,
    Verifier,
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Compiler => write!(f, "compiler"),
            Component::Prover => write!(f, "prover"),
            Component::Solver => write!(f, "solver"),
            Component::Verifier => write!(f, "verifier"),
        }
    }
}

type Test = (Component, String, String);

use std::time::{Duration, Instant};

#[derive(PartialEq, Eq, Debug, Clone)]
enum Time {
    Started(Instant),
    Finished(Duration),
    Restarted(Duration, Instant),
}

pub struct Timer {
    time_log: DashMap<Test, Time>,
    r1cs_log: DashMap<Test, usize>
}

use Time::*;
impl Timer {
    pub fn new() -> Timer {
        Timer {
            time_log: DashMap::new(),
            r1cs_log: DashMap::new(),
        }
    }

    pub fn r1cs(&mut self, comp: Component, test: &str, subtest: &str, nR1cs:usize) {
        if self
            .r1cs_log
            .contains_key(&(comp.clone(), test.to_string(), subtest.to_string()))
        {
           panic!("Trying to write multiple r1cs for same test")
        } else {
            self.r1cs_log.insert(
                (comp, test.to_string(), subtest.to_string()),
                nR1cs,
            );
        }
    }

    pub fn tic(&mut self, comp: Component, test: &str, subtest: &str) {
        if self
            .time_log
            .contains_key(&(comp.clone(), test.to_string(), subtest.to_string()))
        {
            self.time_log.alter(
                &(comp, test.to_string(), subtest.to_string()),
                |_, v| match v {
                    Started(start_time) => Finished(start_time.elapsed()),
                    Finished(duration) => Restarted(duration, Instant::now()),
                    Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
                },
            );
        } else {
            self.time_log.insert(
                (comp, test.to_string(), subtest.to_string()),
                Started(Instant::now()),
            );
        }
    }

    pub fn stop(&mut self) {
        self.time_log.alter_all(|_, v| match v {
            Started(start_time) => Finished(start_time.elapsed()),
            Finished(duration) => Finished(duration),
            Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
        });
    }

    pub fn write_csv(&mut self, out: &str) -> io::Result<()> {
        println!("Writing timer data to {}", out);
        let mut wtr = Writer::from_path(out)?;
        self.stop();
        wtr.write_record(&["Component", "test", "subtest", "metric", "metric_type"])?;
        for ((c, test, subtest), value) in self.time_log.clone().into_iter() {
            if let Finished(duration) = value {
                wtr.write_record(&[
                    c.to_string(),
                    test.to_string(),
                    subtest.to_string(),
                    duration.as_micros().to_string(),
                    "μs".to_string(),
                ])?;
            }
        }
        for ((c, test, subtest), value) in self.r1cs_log.clone().into_iter() {
            wtr.write_record(&[
                c.to_string(),
                test.to_string(),
                subtest.to_string(),
                value.to_string(),
                "constraints".to_string(),
            ])?;
        }
        wtr.flush()?;
        Ok(())
    }
}
