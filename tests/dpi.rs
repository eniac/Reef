
#[cfg(features = "metrics")]
use reef::metrics::{log, log::Component};

#[test]
fn e2e_dpi() {

    #[cfg(features = "metrics")]
    log::tic(Component::Compiler, "bs test", "foo");

    println!("Write this line");

    #[cfg(features = "metrics")]
    log::stop(Component::Compiler, "bs test", "foo");

    #[cfg(features = "metrics")]
    log::r1cs(Component::Compiler, "bs test", "foo",100);

    #[cfg(features = "metrics")]
    log::write_csv("dpi.metrics.csv").unwrap();
}
