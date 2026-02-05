use std::time::Instant;
use vampire_prover::{Function, Options, Predicate, Problem, ProofRes, Term, exists, forall};

fn main() {
    println!("Running index-2 subgroup normality proof benchmark");
    println!(
        "This will run the proof repeatedly to detect memory leaks or performance degradation\n"
    );

    const NUM_ITERATIONS: usize = 1000;
    let mut times = Vec::with_capacity(NUM_ITERATIONS);

    for i in 0..NUM_ITERATIONS {
        waste_symbols(i);
        unsafe {
            vampire_sys::vampire_reset();
        }

        let start = Instant::now();
        let result = run_proof(i);
        let elapsed = start.elapsed();

        times.push(elapsed.as_micros());

        print!("Iteration {:3}: {:6} µs  ", i + 1, elapsed.as_micros());

        match result {
            ProofRes::Proved => print!("[PROVED]"),
            ProofRes::Unprovable => print!("[UNPROVABLE]"),
            ProofRes::Unknown(reason) => print!("[UNKNOWN: {:?}]", reason),
        }

        // Print running statistics every 10 iterations
        if (i + 1) % 10 == 0 {
            let avg = times.iter().sum::<u128>() / times.len() as u128;
            let min = *times.iter().min().unwrap();
            let max = *times.iter().max().unwrap();
            println!("  (avg: {} µs, min: {} µs, max: {} µs)", avg, min, max);
        } else {
            println!();
        }
    }

    // Final statistics
    println!("\n{}", "=".repeat(60));
    println!("Final Statistics:");
    println!("{}", "=".repeat(60));

    let avg = times.iter().sum::<u128>() / times.len() as u128;
    let min = *times.iter().min().unwrap();
    let max = *times.iter().max().unwrap();

    // Calculate standard deviation
    let variance = times
        .iter()
        .map(|&t| {
            let diff = t as i128 - avg as i128;
            (diff * diff) as u128
        })
        .sum::<u128>()
        / times.len() as u128;
    let std_dev = (variance as f64).sqrt();

    println!("Total runs:        {}", NUM_ITERATIONS);
    println!(
        "Average time:      {} µs ({:.2} ms)",
        avg,
        avg as f64 / 1000.0
    );
    println!(
        "Min time:          {} µs ({:.2} ms)",
        min,
        min as f64 / 1000.0
    );
    println!(
        "Max time:          {} µs ({:.2} ms)",
        max,
        max as f64 / 1000.0
    );
    println!(
        "Std deviation:     {:.2} µs ({:.2} ms)",
        std_dev,
        std_dev / 1000.0
    );

    // Check for performance degradation
    let first_10_avg = times[0..10].iter().sum::<u128>() / 10;
    let last_10_avg = times[times.len() - 10..].iter().sum::<u128>() / 10;
    let degradation_percent =
        ((last_10_avg as f64 - first_10_avg as f64) / first_10_avg as f64) * 100.0;

    println!("\nFirst 10 avg:      {} µs", first_10_avg);
    println!("Last 10 avg:       {} µs", last_10_avg);
    println!("Degradation:       {:.2}%", degradation_percent);

    if degradation_percent > 10.0 {
        println!("\n⚠️  WARNING: Significant performance degradation detected!");
        println!("   This may indicate a memory leak or resource accumulation.");
    } else if degradation_percent < -10.0 {
        println!("\n✓ Performance improved over time (likely JIT/cache effects)");
    } else {
        println!("\n✓ Performance stable across iterations");
    }
}

fn waste_symbols(i: usize) {
    for j in 0..1000 {
        Function::new(&format!("p{i}-{j}"), 2);
        Predicate::new(&format!("f{i}-{j}"), 2);
    }
}

fn run_proof(i: usize) -> ProofRes {
    // Prove that every subgroup of index 2 is normal.
    let mult = Function::new(&format!("mult{i}"), 2);
    let inv = Function::new(&format!("inv{i}"), 1);
    let one = Function::constant(&format!("1{i}"));

    // Helper to make multiplication more readable
    let mul = |x: Term, y: Term| -> Term { mult.with(&[x, y]) };

    // Group Axiom 1: Right identity - ∀x. x * 1 = x
    let right_identity = forall(|x| mul(x, one).eq(x));

    // Group Axiom 2: Right inverse - ∀x. x * inv(x) = 1
    let right_inverse = forall(|x| {
        let inv_x = inv.with(&[x]);
        mul(x, inv_x).eq(one)
    });

    // Group Axiom 3: Associativity - ∀x,y,z. (x * y) * z = x * (y * z)
    let associativity = forall(|x| forall(|y| forall(|z| mul(mul(x, y), z).eq(mul(x, mul(y, z))))));

    // Describe the subgroup
    let h = Predicate::new("h", 1);

    // Any subgroup contains the identity
    let h_ident = h.with(&[one]);

    // And is closed under multiplication
    let h_mul_closed =
        forall(|x| forall(|y| (h.with(&[x]) & h.with(&[y])) >> h.with(&[mul(x, y)])));

    // And is closed under inverse
    let h_inv_closed = forall(|x| h.with(&[x]) >> h.with(&[inv.with(&[x])]));

    // H specifically is of order 2
    let h_index_2 = exists(|x| {
        // an element not in H
        let not_in_h = !h.with(&[x]);
        // but everything is in H or x H
        let class = forall(|y| h.with(&[y]) | h.with(&[mul(inv.with(&[x]), y)]));

        not_in_h & class
    });

    // Conjecture: H is normal
    let h_normal = forall(|x| {
        let h_x = h.with(&[x]);
        let conj_x = forall(|y| {
            let y_inv = inv.with(&[y]);
            h.with(&[mul(mul(y, x), y_inv)])
        });
        h_x.iff(conj_x)
    });

    Problem::new(Options::new())
        .with_axiom(right_identity)
        .with_axiom(right_inverse)
        .with_axiom(associativity)
        .with_axiom(h_ident)
        .with_axiom(h_mul_closed)
        .with_axiom(h_inv_closed)
        .with_axiom(h_index_2)
        .conjecture(h_normal)
        .solve()
}
