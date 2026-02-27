use std::time::Duration;
use vampire_prover::{Function, Options, Predicate, Problem, Term, forall};

fn main() {
    let t0 = Function::constant("t0");
    let t2 = Function::constant("t2");
    let t3 = Function::constant("t3");
    let t4 = Function::constant("t4");
    let t50 = Function::constant("t50");
    let t5_fn = Function::new("t5", 2);
    let t5_t2t3: Term = t5_fn.with([t2, t3]);

    let in_ = Predicate::new("in", 2);
    let p39 = Predicate::new("p39", 1);
    let p41 = Predicate::new("p41", 1);
    let p1 = Predicate::new("p1", 2);

    // P1
    let p1_ax1 = in_.with([t3, t0]);
    let p1_ax2 = in_.with([t2, t0]);
    let p1_ax3 = in_.with([t50, t5_t2t3])
        & forall(|x0| in_.with([x0, t5_t2t3]) >> (!t50.eq(x0) >> in_.with([t50, x0])));
    let p1_ax4 = forall(|x0| forall(|x1| forall(|x2| {
        in_.with([x2, t5_fn.with([x1, x0])]).iff(x1.eq(x2) | x0.eq(x2))
    })));
    let p1_ax5 = p39.with(t0) & p41.with(t0);
    let p1_ax6 = t2.eq(t50) | t3.eq(t50);
    let p1_ax7 = !t4.eq(t5_t2t3);
    let p1_ax8 = p1.with([t5_t2t3, t0]);
    let p1_conj = t2.eq(t50) | in_.with([t50, t2]);

    // P2
    let p2_ax1 = t3.eq(t50) | in_.with([t50, t3]);
    let p2_ax2 = in_.with([t2, t0]);
    let p2_ax3 = t2.eq(t50) | t3.eq(t50);
    let p2_ax4 = t2.eq(t50) | in_.with([t50, t2]);
    let p2_ax5 = in_.with([t50, t5_t2t3])
        & forall(|x0| in_.with([x0, t5_t2t3]) >> (!t50.eq(x0) >> in_.with([t50, x0])));
    let p2_ax6 = !t4.eq(t5_t2t3);
    let p2_ax7 = p39.with(t0) & p41.with(t0);
    let p2_ax8 = in_.with([t3, t0]);
    let p2_ax9 = p1.with([t5_t2t3, t0]);
    let p2_conj = in_.with([t3, t2]) | (t2.eq(t3) | in_.with([t2, t3]));

    let mut opts1 = Options::new();
    opts1.timeout(Duration::from_millis(50));

    let r1 = Problem::new(opts1)
        .with_axiom(p1_ax1).with_axiom(p1_ax2).with_axiom(p1_ax3).with_axiom(p1_ax4)
        .with_axiom(p1_ax5).with_axiom(p1_ax6).with_axiom(p1_ax7).with_axiom(p1_ax8)
        .conjecture(p1_conj)
        .solve();
    println!("P1 (50ms): {:?}", r1);

    // Try P2 with a 5-second timeout
    let mut opts2_long = Options::new();
    opts2_long.timeout(Duration::from_secs(5));

    let r2_long = Problem::new(opts2_long)
        .with_axiom(p2_ax1).with_axiom(p2_ax2).with_axiom(p2_ax3).with_axiom(p2_ax4)
        .with_axiom(p2_ax5).with_axiom(p2_ax6).with_axiom(p2_ax7).with_axiom(p2_ax8)
        .with_axiom(p2_ax9).conjecture(p2_conj)
        .solve();
    println!("P2 (5s, after P1): {:?}", r2_long);
}
