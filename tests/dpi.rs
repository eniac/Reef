use reef::metrics::{log, log::Component};

#[test]
fn e2e_dpi() {
    log::tic(Component::Compiler, "bs test", "foo");
    println!("Write this line");
    log::stop(Component::Compiler, "bs test", "foo");

    log::r1cs(Component::Compiler, "bs test", "foo",100);
    println!("Write this line");

    if let Err(e) = log::write_csv("foo.csv") {
        eprintln!("Error writing to file: {}", e);
        panic!("exiting");
    }
}

