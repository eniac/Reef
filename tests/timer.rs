use csv::Writer;
use dashmap::DashMap;
use std::fmt::Display;
use std::fs::OpenOptions;
use std::io;

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
    log: DashMap<Test, Time>,
}

use Time::*;
impl Timer {
    pub fn new() -> Timer {
        Timer {
            log: DashMap::new(),
        }
    }

    pub fn tic(&mut self, comp: Component, test: &str, subtest: &str) {
        if self
            .log
            .contains_key(&(comp.clone(), test.to_string(), subtest.to_string()))
        {
            self.log.alter(
                &(comp, test.to_string(), subtest.to_string()),
                |_, v| match v {
                    Started(start_time) => Finished(start_time.elapsed()),
                    Finished(duration) => Restarted(duration, Instant::now()),
                    Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
                },
            );
        } else {
            self.log.insert(
                (comp, test.to_string(), subtest.to_string()),
                Started(Instant::now()),
            );
        }
    }

    pub fn stop(&mut self) {
        self.log.alter_all(|_, v| match v {
            Started(start_time) => Finished(start_time.elapsed()),
            Finished(duration) => Finished(duration),
            Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
        });
    }

    pub fn write_csv(&mut self, out: &str) -> io::Result<()> {
        println!("Writing timer data to {}", out);
        let mut file = OpenOptions::new().write(true).append(true).open(out).unwrap();
        let mut wtr = Writer::from_writer(file)?;
        self.stop();
        wtr.write_record(&["Component", "test", "subtest", "time (μs)"])?;
        for ((c, test, subtest), value) in self.log.clone().into_iter() {
            if let Finished(duration) = value {
                wtr.write_record(&[
                    c.to_string(),
                    test.to_string(),
                    subtest.to_string(),
                    duration.as_micros().to_string(),
                ])?;
            }
        }
        wtr.flush()?;
        Ok(())
    }
}
