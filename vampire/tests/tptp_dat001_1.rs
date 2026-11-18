#![cfg(feature = "integrated-prover")]

use vampire_prover::ffi::*;
use vampire_prover::Options;

// All tests in this file share Vampire's global state, so they must not run concurrently.
static TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[test]
fn test_tptp_dat001_1_combined() {
    let _guard = TEST_LOCK.lock().unwrap();
    // Safety: Reset global state
    unsafe {
        vampire_sys::vampire_reset();
    }

    {
        // Part 1: DAT001_1.p
        let list = Sort::new("list");
        let int = Sort::int();

        let nil = Function::typed("nil", &[], list.clone());
        let mycons = Function::typed("mycons", &[int.clone(), list.clone()], list.clone());
        let sorted = Predicate::typed("sorted", &[list.clone()]);
        let less = Predicate::interpreted("$less", Interp::IntLess);

        let c1 = Term::int("1");
        let c2 = Term::int("2");
        let c4 = Term::int("4");
        let c7 = Term::int("7");
        let c100 = Term::int("100");

        let mut options = Options::new();
        options.timeout(std::time::Duration::from_secs(2));
        let mut problem = Problem::new(options);
        problem.with_axiom(sorted.with(nil.with(&[])));
        problem.with_axiom(forall_typed(int.clone(), |x| {
            sorted.with(mycons.with([x, nil.with(&[])]))
        }));
        problem.with_axiom(forall_typed(int.clone(), |x| {
            forall_typed(int.clone(), |y| {
                forall_typed(list.clone(), |r| {
                    (less.with([x, y]) & sorted.with(mycons.with([y, r.clone()])))
                        >> sorted.with(mycons.with([x, mycons.with([y, r])]))
                })
            })
        }));

        let l100 = mycons.with([c100, nil.with(&[] as &[Term])]);
        let l7 = mycons.with([c7, l100]);
        let l4 = mycons.with([c4, l7]);
        let l2 = mycons.with([c2, l4]);
        let l1 = mycons.with([c1, l2]);
        let conjecture = sorted.with(l1);

        problem.conjecture(conjecture);
        assert_eq!(problem.solve(), ProofRes::Proved);
    }

    // Prepare for next part without full reset
    unsafe { vampire_sys::vampire_prepare_for_next_proof(); }

    {
        // Part 2: Ergonomic arithmetic
        let _int = Sort::int();
        let plus = Function::interpreted("$sum", Interp::IntPlus);
        let less = Predicate::interpreted("$less", Interp::IntLess);

        let one = 1;
        let two = 2;
        let three = 3;

        let formula = less.with((plus.with([one, two]), three));
        let mut problem = Problem::new(Options::new());
        problem.conjecture(formula);
        let result = problem.solve();
        assert!(matches!(result, ProofRes::Unprovable | ProofRes::Unknown(_)));

        let formula2 = plus.with([one, two]).eq(three.into_term());
        let mut problem2 = Problem::new(Options::new());
        problem2.conjecture(formula2);
        assert_eq!(problem2.solve(), ProofRes::Proved);
    }

    unsafe { vampire_sys::vampire_prepare_for_next_proof(); }

    {
        // Part 3: Ergonomic real arithmetic
        let _real = Sort::real();
        let plus = Function::interpreted("$sum", Interp::RealPlus);
        let less = Predicate::interpreted("$less", Interp::RealLess);

        let one_point_five = 1.5;
        let two_point_five = 2.5;
        let four_point_zero = 4.0;

        // 1.5 + 2.5 < 4.0 is false
        let formula = less.with((plus.with([one_point_five, two_point_five]), four_point_zero));

        let mut problem = Problem::new(Options::new());
        problem.conjecture(formula);

        let result = problem.solve();
        assert!(matches!(result, ProofRes::Unprovable | ProofRes::Unknown(_)));

        // 1.5 + 2.5 = 4.0 is true
        let formula2 = plus.with([one_point_five, two_point_five]).eq(four_point_zero.into_term());

        let mut problem2 = Problem::new(Options::new());
        problem2.conjecture(formula2);
        assert_eq!(problem2.solve(), ProofRes::Proved);
    }
}

#[test]
fn test_clausification() {
    let _guard = TEST_LOCK.lock().unwrap();
    unsafe {
        vampire_sys::vampire_prepare_for_next_proof();
    }

    let p = Predicate::new("P", 1);
    let q = Predicate::new("Q", 1);
    let x = Term::new_var(0);

    {
        // Formula: P(x) | Q(x)
        // CNF should be: {P(x), Q(x)}
        let formula = p.with(x) | q.with(x);
        let mut problem = Problem::new(Options::new());
        problem.with_axiom(formula);
        println!("Calling clausify Part 1...");
        let clauses = problem.clausify();
        assert_eq!(clauses.len(), 1);
        let s0 = &clauses[0];
        println!("Clause string: '{}'", s0);
        // Vampire wraps predicate names in single quotes: 'P'(X0)
        assert!(s0.to_lowercase().contains("'p'(x0)") && s0.to_lowercase().contains("'q'(x0)"));
    }

    // Use prepare_for_next_proof instead of reset inside a test
    unsafe {
        vampire_sys::vampire_prepare_for_next_proof();
    }

    {
        // Formula: P(x) <=> Q(x)
        // CNF should be: {~P(x), Q(x)} and {~Q(x), P(x)}
        let formula = p.with(x).iff(q.with(x));
        let mut problem = Problem::new(Options::new());
        problem.with_axiom(formula);
        println!("Calling clausify Part 2...");
        let clauses = problem.clausify();
        assert_eq!(clauses.len(), 2);
    }
}
