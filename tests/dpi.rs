use reef::metrics::*;

#[test]
fn e2e_dpi() {
    TIMER.tic(Component::Compiler, "bs test", "foo");
    println!("Write this line");
    TIMER.stop(Component::Compiler, "bs test", "foo");

    TIMER.r1cs(Component::Compiler, "bs test", "foo",100);
    println!("Write this line");

    if let Err(e) = TIMER.write_csv("foo.csv") {
        eprintln!("Error writing to file: {}", e);
        panic!("exiting");
    }
}

