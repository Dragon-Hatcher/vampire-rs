use std::time::Duration;
use vampire_prover::{
    Function, Options, Predicate, Problem, ProofRes, UnknownReason, exists, forall,
};

#[test]
fn timeout_works() {
    // This is the repro problem that causes vampire to hang
    // With a 1 second timeout, it should return Timeout instead of hanging
    let v_in = Predicate::new("in", 2);
    let v2 = Function::new("v2", 1);
    let v3 = Function::new("v3", 2);
    let v1 = Function::constant("v1");
    let v0 = Function::constant("v0");

    // Axiom: ! [X0] : ! [X1] : (in(X1,v2(X0)) <=> ? [X2] : (in(X1,X2) & in(X2,X0)))
    let axiom = forall(|x0| {
        forall(|x1| {
            let lhs = v_in.with([x1, v2.with(x0)]);
            let rhs = exists(|x2| v_in.with([x1, x2]) & v_in.with([x2, x0]));
            lhs.iff(rhs)
        })
    });

    // Conjecture: ! [X0] : (in(X0,v3(v1,v0)) <=> (in(X0,v1) | in(X0,v0)))
    let conjecture = forall(|x0| {
        let lhs = v_in.with([x0, v3.with([v1, v0])]);
        let rhs = v_in.with([x0, v1]) | v_in.with([x0, v0]);
        lhs.iff(rhs)
    });

    let mut opts = Options::new();
    opts.timeout(Duration::from_secs(1));

    let solution = Problem::new(opts)
        .with_axiom(axiom)
        .conjecture(conjecture)
        .solve();

    // Should timeout, not hang or exit the process
    assert_eq!(solution, ProofRes::Unknown(UnknownReason::Timeout));
}
