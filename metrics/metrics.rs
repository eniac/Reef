pub mod log {
    use csv::Writer;
    use dashmap::DashMap;
    use std::fmt::Display;
    use std::io::Result;
    use std::time::{Duration, Instant};
    use std::fs::OpenOptions;
    use std::path::Path;
    use lazy_static::lazy_static;



    lazy_static! {
        pub static ref TIMER: DashMap<Test, Time> = DashMap::new();
        pub static ref R1CS: DashMap<Test, usize> = DashMap::new();
        pub static ref SPACE: DashMap<Test, usize> = DashMap::new();
    }

    #[derive(PartialEq, Eq, Debug, Hash, Clone)]
    pub enum Component {
        Compiler,
        Prover,
        Solver,
        Verifier,
        CommitmentGen,
    }

    impl Display for Component {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Component::Compiler => write!(f, "C"),
                Component::Prover => write!(f, "P"),
                Component::Solver => write!(f, "S"),
                Component::Verifier => write!(f, "V"),
                Component::CommitmentGen => write!(f,"CG"),
            }
        }
    }

    #[derive(PartialEq, Eq, Debug, Hash, Clone)]
    pub enum TestType {
        Constraints,
        Runtime,
        Size
    }

    impl Display for TestType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                TestType::Constraints => write!(f, "NOC"),
                TestType::Runtime => write!(f, "R"),
                TestType::Size => write!(f, "S"),
            }
        }
    }

    pub type Test = (TestType,Component, String);

    #[derive(PartialEq, Eq, Debug, Clone)]
    pub enum Time {
        Started(Instant),
        Finished(Duration),
        Restarted(Duration, Instant),
    }

    use Time::*;
    pub fn r1cs(comp: Component, test: &str, num_constraints: usize) {
        if R1CS.contains_key(&(TestType::Constraints,comp.clone(), test.to_string())) {
            panic!("Trying to write multiple r1cs for same test")
        } else {
            R1CS.insert(
                (TestType::Constraints,comp, test.to_string()),
                num_constraints,
            );
        }
    }

    pub fn space(comp: Component, test: &str,  sz_bytes: usize) {
        if SPACE.contains_key(&(TestType::Size, comp.clone(), test.to_string())) {
            panic!("Trying to write multiple sizes for same test")
        } else {
            SPACE.insert((TestType::Size,comp, test.to_string()), sz_bytes);
        }
    }

    pub fn tic(comp: Component, test: &str) {
        if TIMER.contains_key(&(TestType::Runtime,comp.clone(), test.to_string())) {
            TIMER.alter(
                &(TestType::Runtime,comp, test.to_string()),
                |_, v| match v {
                    Started(start_time) => Finished(start_time.elapsed()),
                    Finished(duration) => Restarted(duration, Instant::now()),
                    Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
                },
            );
        } else {
            TIMER.insert(
                (TestType::Runtime, comp, test.to_string()),
                Started(Instant::now()),
            );
        }
    }

    pub fn stop(comp: Component, test: &str) {
        TIMER.alter(
            &(TestType::Runtime, comp, test.to_string()),
            |_, v| match v {
                Started(start_time) => Finished(start_time.elapsed()),
                Finished(duration) => Finished(duration),
                Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
            },
        );
    }

    pub fn write_csv(out: &str) -> Result<()> {
      println!("Writing timer data to {}", out);
      let mut write_header = true;
      if Path::new(&out).exists() {
        write_header = false;
      }
      let file = OpenOptions::new().write(true).append(true).create(true).open(out).unwrap();
        let mut wtr = Writer::from_writer(file);

        TIMER.alter_all(|_, v| match v {
            Started(start_time) => Finished(start_time.elapsed()),
            Finished(duration) => Finished(duration),
            Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
        });

        if write_header {
            wtr.write_record(&["type", "component", "test", "value", "metric_type"])?;
        }

        for ((test_type, c, test), value) in TIMER.clone().into_iter() {
            if let Finished(duration) = value {
                wtr.write_record(&[
                    test_type.to_string(),
                    c.to_string(),
                    test.to_string(),
                    duration.as_micros().to_string(),
                    "μs".to_string(),
                ])?;
            }
        }
        println!("times");
        for ((test_type, c, test), value) in R1CS.clone().into_iter() {
            wtr.write_record(&[
                test_type.to_string(),
                c.to_string(),
                test.to_string(),
                value.to_string(),
                "constraints".to_string(),
            ])?;
        }
        println!("r1cs");

        for ((test_type, c, test), value) in SPACE.clone().into_iter() {
            wtr.write_record(&[
                test_type.to_string(),
                c.to_string(),
                test.to_string(),
                value.to_string(),
                "bytes".to_string(),
            ])?;
        }
        println!("space");
        wtr.flush()?;
        TIMER.clear();
        R1CS.clear();
        SPACE.clear();
        Ok(())
    }
}
