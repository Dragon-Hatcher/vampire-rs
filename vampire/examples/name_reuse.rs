use vampire_prover::{Function, Predicate, Problem};

fn main() {
    let x1 = Function::new("x", 0);
    let x2 = Function::new("x", 0);

    dbg!(x1, x2);
    dbg!(x1 == x2);

    let y1 = Function::new("y", 0);
    let y2 = Function::new("y", 1);

    dbg!(y1, y2);

    let z1 = Function::new("z", 0);
    let z2 = Predicate::new("z", 0);

    dbg!(z1, z2);

    let solution = Problem::new()
        .with_axiom(y1.with(&[]).eq(y2.with(&[y1.with(&[])])))
        .solve();

    dbg!(solution);
}
