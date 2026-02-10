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

#[test]
fn timeout_works2() {
    // New problem found that causes vampire to stall
    // With a 50ms timeout, it should return Timeout instead of hanging
    let v_in = Predicate::new("in", 2);
    let v6 = Function::new("v6", 1);
    let v3 = Function::new("v3", 2);
    let v1 = Function::constant("v1");
    let v2 = Function::constant("v2");
    let v0 = Function::constant("v0");
    let false_pred = Predicate::new("false", 0);

    // Axiom 1: ! [X0] : (~v0 = X0 => ! [X1] : (in(X1,v6(X0)) <=> ! [X2] : (in(X2,X0) => in(X1,X2))))
    let axiom1 = forall(|x0| {
        let condition = !v0.eq(x0);
        let inner = forall(|x1| {
            let lhs = v_in.with([x1, v6.with(x0)]);
            let rhs = forall(|x2| {
                let premise = v_in.with([x2, x0]);
                let conclusion = v_in.with([x1, x2]);
                premise >> conclusion
            });
            lhs.iff(rhs)
        });
        condition >> inner
    });

    // Axiom 2: ~false (always true)
    let axiom2 = !false_pred.with([]);

    // Conjecture: ! [X0] : (in(X0,v6(v3(v1,v2))) <=> ! [X1] : (in(X1,v3(v1,v2)) => in(X0,X1)))
    let conjecture = forall(|x0| {
        let lhs = v_in.with([x0, v6.with(v3.with([v1, v2]))]);
        let rhs = forall(|x1| {
            let premise = v_in.with([x1, v3.with([v1, v2])]);
            let conclusion = v_in.with([x0, x1]);
            premise >> conclusion
        });
        lhs.iff(rhs)
    });

    let mut opts = Options::new();
    opts.timeout(Duration::from_millis(50));

    let solution = Problem::new(opts)
        .with_axiom(axiom1)
        .with_axiom(axiom2)
        .conjecture(conjecture)
        .solve();

    // Should timeout, not hang or exit the process.
    // With a very short timeout the result could be Timeout or Incomplete
    // (if Vampire exhausts the search space before the timer fires).
    assert!(
        solution == ProofRes::Unknown(UnknownReason::Timeout)
            || solution == ProofRes::Unknown(UnknownReason::Incomplete),
        "Expected Timeout or Incomplete, got {:?}",
        solution
    );
}
