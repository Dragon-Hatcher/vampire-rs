#![cfg(feature = "integrated-prover")]

use vampire_prover::Options;
use vampire_prover::ffi::*;

// Vampire's global state is shared, so these tests must not run concurrently.
static TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[test]
fn proof_steps_name_their_input_axioms() {
    let _guard = TEST_LOCK.lock().unwrap();
    let is_mortal = Predicate::new("mortal", 1);
    let is_man = Predicate::new("man", 1);
    let unused = Predicate::new("unused", 1);
    let socrates = Function::constant("socrates");

    let (result, proof) = Problem::new(Options::new())
        .with_named_axiom(is_man.with(socrates), "socrates_is_man")
        .with_axiom(unused.with(socrates))
        .with_named_axiom(
            forall(|x| is_man.with(x) >> is_mortal.with(x)),
            "men_are_mortal",
        )
        .conjecture(is_mortal.with(socrates))
        .solve_and_prove();
    assert_eq!(result, ProofRes::Proved);
    let proof = proof.expect("a proof");

    let mut inputs: Vec<(usize, Option<&str>)> = proof
        .steps()
        .iter()
        .filter_map(|s| s.axiom_index().map(|i| (i, s.axiom_name())))
        .collect();
    inputs.sort();
    assert_eq!(
        inputs,
        [(0, Some("socrates_is_man")), (2, Some("men_are_mortal"))]
    );

    // Only input-axiom steps are attributed: derived steps and the negated
    // conjecture carry neither an index nor a name.
    for step in proof.steps() {
        if step.rule() != ProofRule::Axiom {
            assert_eq!(step.axiom_index(), None);
            assert_eq!(step.axiom_name(), None);
        }
    }
}

#[test]
fn unnamed_axioms_are_indexed_without_a_name() {
    let _guard = TEST_LOCK.lock().unwrap();
    let p = Predicate::new("p", 1);
    let x = Function::constant("x");

    let (result, proof) = Problem::new(Options::new())
        .with_axiom(p.with(x))
        .conjecture(p.with(x))
        .solve_and_prove();
    assert_eq!(result, ProofRes::Proved);
    let proof = proof.expect("a proof");
    let step = proof
        .steps()
        .iter()
        .find(|s| s.axiom_index().is_some())
        .expect("the axiom is used");
    assert_eq!(step.axiom_index(), Some(0));
    assert_eq!(step.axiom_name(), None);
}

#[test]
fn attribution_is_per_solve() {
    let _guard = TEST_LOCK.lock().unwrap();
    let p = Predicate::new("q", 1);
    let x = Function::constant("y");

    let mut problem = Problem::new(Options::new());
    problem
        .with_named_axiom(p.with(x), "first")
        .conjecture(p.with(x));
    let (_, first) = problem.solve_and_prove();
    let (_, second) = problem.solve_and_prove();
    for proof in [first, second] {
        let names: Vec<&str> = proof
            .as_ref()
            .expect("a proof")
            .steps()
            .iter()
            .filter_map(|s| s.axiom_name())
            .collect();
        assert_eq!(names, ["first"]);
    }
}
