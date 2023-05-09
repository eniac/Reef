pub mod log {
  use dashmap::DashMap;
  use std::fmt::Display;
  use std::io::Result;
  use std::time::{Duration, Instant};
  use csv::Writer;

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

  pub type Test = (Component, String, String);

  #[derive(PartialEq, Eq, Debug, Clone)]
  pub enum Time {
      Started(Instant),
      Finished(Duration),
      Restarted(Duration, Instant),
  }

  use Time::*;
  pub fn r1cs(comp: Component, test: &str, subtest: &str, num_constraints:usize) {
      if R1CS.contains_key(&(comp.clone(), test.to_string(), subtest.to_string())) {
         panic!("Trying to write multiple r1cs for same test")
      } else {
          R1CS.insert(
              (comp, test.to_string(), subtest.to_string()),
              num_constraints,
          );
      }
  }

  pub fn space(comp: Component, test: &str, subtest: &str, sz_bytes:usize) {
      if SPACE.contains_key(&(comp.clone(), test.to_string(), subtest.to_string())) {
         panic!("Trying to write multiple sizes for same test")
      } else {
          SPACE.insert(
              (comp, test.to_string(), subtest.to_string()),
              sz_bytes,
          );
      }
  }

  pub fn tic(comp: Component, test: &str, subtest: &str) {
      if TIMER.contains_key(&(comp.clone(), test.to_string(), subtest.to_string())) {
        TIMER.alter(
              &(comp, test.to_string(), subtest.to_string()),
              |_, v| match v {
                  Started(start_time) => Finished(start_time.elapsed()),
                  Finished(duration) => Restarted(duration, Instant::now()),
                  Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
              },
          );
      } else {
        TIMER.insert(
              (comp, test.to_string(), subtest.to_string()),
              Started(Instant::now()),
          );
      }
  }

  pub fn stop(comp: Component, test: &str, subtest: &str) {
      TIMER.alter(&(comp, test.to_string(), subtest.to_string()),
      |_, v| match v{
          Started(start_time) => Finished(start_time.elapsed()),
          Finished(duration) => Finished(duration),
          Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
      });
  }

  pub fn write_csv(out: &str) -> Result<()> {
      println!("Writing timer data to {}", out);
      let mut wtr = Writer::from_path(out)?;

      TIMER.alter_all(|_, v| match v {
          Started(start_time) => Finished(start_time.elapsed()),
          Finished(duration) => Finished(duration),
          Restarted(duration, start_time) => Finished(duration + start_time.elapsed()),
      });

      wtr.write_record(&["Component", "test", "subtest", "metric", "metric_type"])?;
      for ((c, test, subtest), value) in TIMER.clone().into_iter() {
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
      for ((c, test, subtest), value) in R1CS.clone().into_iter() {
          wtr.write_record(&[
              c.to_string(),
              test.to_string(),
              subtest.to_string(),
              value.to_string(),
              "constraints".to_string(),
          ])?;
      }

      for ((c, test, subtest), value) in SPACE.clone().into_iter() {
          wtr.write_record(&[
              c.to_string(),
              test.to_string(),
              subtest.to_string(),
              value.to_string(),
              "bytes".to_string(),
          ])?;
      }
      wtr.flush()?;
      Ok(())
  }
}
