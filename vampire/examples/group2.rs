use vampire_prover::{Function, Options, Predicate, Problem, ProofRes, Term, exists, forall};

fn main() {
    // Prove that every subgroup of index 2 is normal.
    let mult = Function::new("mult", 2);
    let inv = Function::new("inv", 1);
    let one = Function::constant("1");

    // Helper to make multiplication more readable
    let mul = |x: Term, y: Term| -> Term { mult.with([x, y]) };

    // Group Axiom 1: Right identity - ∀x. x * 1 = x
    let right_identity = forall(|x| mul(x, one).eq(x));

    // Group Axiom 2: Right inverse - ∀x. x * inv(x) = 1
    let right_inverse = forall(|x| {
        let inv_x = inv.with(x);
        mul(x, inv_x).eq(one)
    });

    // Group Axiom 3: Associativity - ∀x,y,z. (x * y) * z = x * (y * z)
    let associativity = forall(|x| forall(|y| forall(|z| mul(mul(x, y), z).eq(mul(x, mul(y, z))))));

    // Describe the subgroup
    let h = Predicate::new("h", 1);

    // Any subgroup contains the identity
    let h_ident = h.with(one);

    // And is closed under multiplication
    let h_mul_closed = forall(|x| forall(|y| (h.with(x) & h.with(y)) >> h.with(mul(x, y))));

    // And is closed under inverse
    let h_inv_closed = forall(|x| h.with(x) >> h.with(inv.with(x)));

    // H specifically is of order 2
    let h_index_2 = exists(|x| {
        // an element not in H
        let not_in_h = !h.with(x);
        // but everything is in H or x H
        let class = forall(|y| h.with(y) | h.with(mul(inv.with(x), y)));

        not_in_h & class
    });

    // Conjecture: H is normal
    let h_normal = forall(|x| {
        let h_x = h.with(x);
        let conj_x = forall(|y| {
            let y_inv = inv.with(y);
            h.with(mul(mul(y, x), y_inv))
        });
        h_x.iff(conj_x)
    });

    let (solution, proof) = Problem::new(Options::new())
        .with_axiom(right_identity)
        .with_axiom(right_inverse)
        .with_axiom(associativity)
        .with_axiom(h_ident)
        .with_axiom(h_mul_closed)
        .with_axiom(h_inv_closed)
        .with_axiom(h_index_2)
        .conjecture(h_normal)
        .solve_and_prove();

    if let Some(proof) = proof {
        println!("{}", proof);
    }

    assert_eq!(solution, ProofRes::Proved);
}
