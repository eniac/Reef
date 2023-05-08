use reef::metrics::{Timer, Component};

#[test]
fn e2e_dpi() {
    let mut timer = Timer::new();
    timer.tic(Component::Compiler, "bs test", "foo");
    println!("Write this line");
    timer.stop();

    timer.r1cs(Component::Compiler, "bs test", "foo",100);
    println!("Write this line");

    if let Err(e) = timer.write_csv("foo.csv") {
        eprintln!("Error writing to file: {}", e);
        panic!("exiting");
    }
}

