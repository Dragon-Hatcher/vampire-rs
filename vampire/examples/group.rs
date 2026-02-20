use vampire_prover::{Function, Options, Problem, ProofRes, Term, forall};

fn main() {
    // Prove that the identity element works on the left using group axioms
    // In group theory, if we define a group with:
    //   - Right identity: x * 1 = x
    //   - Right inverse: x * inv(x) = 1
    //   - Associativity: (x * y) * z = x * (y * z)
    // Then we can prove the left identity: 1 * x = x

    let mult = Function::new("mult", 2);
    let inv = Function::new("inv", 1);
    let one = Function::constant("1");

    // Helper to make multiplication more readable
    let mul = |x: Term, y: Term| -> Term { mult.with([x, y]) };

    // Axiom 1: Right identity - ∀x. x * 1 = x
    let right_identity = forall(|x| mul(x, one).eq(x));

    // Axiom 2: Right inverse - ∀x. x * inv(x) = 1
    let right_inverse = forall(|x| {
        let inv_x = inv.with(x);
        mul(x, inv_x).eq(one)
    });

    // Axiom 3: Associativity - ∀x,y,z. (x * y) * z = x * (y * z)
    let associativity = forall(|x| forall(|y| forall(|z| mul(mul(x, y), z).eq(mul(x, mul(y, z))))));

    // Conjecture: Left identity - ∀x. 1 * x = x
    let left_identity = forall(|x| mul(one, x).eq(x));

    let (solution, proof) = Problem::new(Options::new())
        .with_axiom(right_identity)
        .with_axiom(right_inverse)
        .with_axiom(associativity)
        .conjecture(left_identity)
        .solve_and_prove();

    if let Some(proof) = proof {
        println!("{}", proof);
    }

    assert_eq!(solution, ProofRes::Proved);
}
