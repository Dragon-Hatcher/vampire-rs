use crate::lock::synced;
use std::{
    ffi::CString,
    ops::{BitAnd, BitOr, Not, Shr},
};
use vampire_sys as sys;

mod lock;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Function {
    id: u32,
    arity: u32,
}

impl Function {
    pub fn new(name: &str, arity: u32) -> Self {
        synced(|_| {
            let name = CString::new(name).expect("valid c string");
            let function = unsafe { sys::vampire_add_function(name.as_ptr(), arity) };
            Self {
                id: function,
                arity,
            }
        })
    }
    pub fn arity(&self) -> u32 {
        self.arity
    }

    pub fn constant(name: &str) -> Term {
        Self::new(name, 0).with(&[])
    }

    pub fn with(&self, args: &[Term]) -> Term {
        Term::new_function(*self, args)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Predicate {
    id: u32,
    arity: u32,
}

impl Predicate {
    pub fn new(name: &str, arity: u32) -> Self {
        // TODO: predicate/term with same name already exists?

        synced(|_| {
            let name = CString::new(name).expect("valid c string");
            let predicate = unsafe { sys::vampire_add_predicate(name.as_ptr(), arity) };
            Self {
                id: predicate,
                arity,
            }
        })
    }

    pub fn arity(&self) -> u32 {
        self.arity
    }

    pub fn with(&self, args: &[Term]) -> Formula {
        Formula::new_predicate(*self, args)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Term {
    id: *mut sys::vampire_term_t,
}

impl Term {
    pub fn new_function(func: Function, args: &[Term]) -> Self {
        // TODO: try_new_function?
        assert!(args.len() == func.arity() as usize);

        synced(|_| unsafe {
            let arg_count = args.len();
            let args = std::mem::transmute(args.as_ptr());
            let term = sys::vampire_term(func.id, args, arg_count);
            Self { id: term }
        })
    }

    pub fn new_var(idx: u32) -> Self {
        synced(|info| unsafe {
            info.free_var = info.free_var.max(idx + 1);
            let term = sys::vampire_var(idx);
            Self { id: term }
        })
    }

    pub fn free_var() -> (Self, u32) {
        synced(|info| unsafe {
            let idx = info.free_var;
            info.free_var += 1;
            let term = sys::vampire_var(idx);
            (Self { id: term }, idx)
        })
    }

    pub fn eq(&self, rhs: Term) -> Formula {
        Formula::new_eq(*self, rhs)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Formula {
    id: *mut sys::vampire_formula_t,
}

impl Formula {
    pub fn new_predicate(pred: Predicate, args: &[Term]) -> Self {
        assert!(args.len() == pred.arity() as usize);

        synced(|_| unsafe {
            let arg_count = args.len();
            let args = std::mem::transmute(args.as_ptr());
            let lit = sys::vampire_lit(pred.id, true, args, arg_count);
            let atom = sys::vampire_atom(lit);
            Self { id: atom }
        })
    }

    pub fn new_eq(lhs: Term, rhs: Term) -> Self {
        synced(|_| unsafe {
            let lit = sys::vampire_eq(true, lhs.id, rhs.id);
            let atom = sys::vampire_atom(lit);
            Self { id: atom }
        })
    }

    pub fn new_and(formulas: &[Formula]) -> Self {
        synced(|_| unsafe {
            let formula_count = formulas.len();
            let formulas = std::mem::transmute(formulas.as_ptr());
            let id = sys::vampire_and(formulas, formula_count);
            Self { id }
        })
    }

    pub fn new_or(formulas: &[Formula]) -> Self {
        synced(|_| unsafe {
            let formula_count = formulas.len();
            let formulas = std::mem::transmute(formulas.as_ptr());
            let id = sys::vampire_or(formulas, formula_count);
            Self { id }
        })
    }

    pub fn new_not(formula: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_not(formula.id) };
            Self { id }
        })
    }

    pub fn new_forall(var: u32, f: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_forall(var, f.id) };
            Self { id }
        })
    }

    pub fn new_exists(var: u32, f: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_exists(var, f.id) };
            Self { id }
        })
    }

    pub fn imp(&self, rhs: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_imp(self.id, rhs.id) };
            Self { id }
        })
    }

    pub fn iff(&self, rhs: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_iff(self.id, rhs.id) };
            Self { id }
        })
    }
}

pub fn forall<F: FnOnce(Term) -> Formula>(f: F) -> Formula {
    let (var, var_idx) = Term::free_var();
    let f = f(var);
    Formula::new_forall(var_idx, f)
}

pub fn exists<F: FnOnce(Term) -> Formula>(f: F) -> Formula {
    let (var, var_idx) = Term::free_var();
    let f = f(var);
    Formula::new_exists(var_idx, f)
}

impl BitAnd for Formula {
    type Output = Formula;

    fn bitand(self, rhs: Self) -> Self::Output {
        Formula::new_and(&[self, rhs])
    }
}

impl BitOr for Formula {
    type Output = Formula;

    fn bitor(self, rhs: Self) -> Self::Output {
        Formula::new_or(&[self, rhs])
    }
}

impl Not for Formula {
    type Output = Formula;

    fn not(self) -> Self::Output {
        Formula::new_not(self)
    }
}

impl Shr for Formula {
    type Output = Formula;

    fn shr(self, rhs: Self) -> Self::Output {
        self.imp(rhs)
    }
}

#[derive(Debug, Clone)]
pub struct Problem {
    axioms: Vec<Formula>,
    conjecture: Option<Formula>,
}

impl Problem {
    pub fn new() -> Self {
        Self {
            axioms: Vec::new(),
            conjecture: None,
        }
    }

    pub fn with_axiom(mut self, f: Formula) -> Self {
        self.axioms.push(f);
        self
    }

    pub fn conjecture(mut self, f: Formula) -> Self {
        self.conjecture = Some(f);
        self
    }

    pub fn solve(self) -> ProofRes {
        synced(|_| unsafe {
            let mut units = Vec::new();

            for axiom in self.axioms {
                let axiom_unit = sys::vampire_axiom_formula(axiom.id);
                units.push(axiom_unit);
            }
            if let Some(conjecture) = self.conjecture {
                let conjecture_unit = sys::vampire_conjecture_formula(conjecture.id);
                units.push(conjecture_unit);
            }

            sys::vampire_prepare_for_next_proof();
            let problem = sys::vampire_problem_from_units(units.as_mut_ptr(), units.len());
            let proof_res = sys::vampire_prove(problem);

            ProofRes::new_from_raw(proof_res)
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofRes {
    Proved,
    Unprovable,
    Unknown(UnknownReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnknownReason {
    Timeout,
    MemoryLimit,
    Incomplete,
    Unknown,
}

impl ProofRes {
    fn new_from_raw(idx: u32) -> ProofRes {
        if idx == sys::vampire_proof_result_t_VAMPIRE_PROOF {
            ProofRes::Proved
        } else if idx == sys::vampire_proof_result_t_VAMPIRE_SATISFIABLE {
            ProofRes::Unprovable
        } else if idx == sys::vampire_proof_result_t_VAMPIRE_TIMEOUT {
            ProofRes::Unknown(UnknownReason::Timeout)
        } else if idx == sys::vampire_proof_result_t_VAMPIRE_MEMORY_LIMIT {
            ProofRes::Unknown(UnknownReason::MemoryLimit)
        } else if idx == sys::vampire_proof_result_t_VAMPIRE_INCOMPLETE {
            ProofRes::Unknown(UnknownReason::Incomplete)
        } else if idx == sys::vampire_proof_result_t_VAMPIRE_UNKNOWN {
            ProofRes::Unknown(UnknownReason::Unknown)
        } else {
            panic!()
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Function, Predicate, Problem, ProofRes, Term, exists, forall};

    #[test]
    fn socrates_proof() {
        // Classic Socrates syllogism
        let is_mortal = Predicate::new("mortal", 1);
        let is_man = Predicate::new("man", 1);

        // All men are mortal
        let men_are_mortal = forall(|x| is_man.with(&[x]) >> is_mortal.with(&[x]));

        // Socrates is a man
        let socrates = Function::constant("socrates");
        let socrates_is_man = is_man.with(&[socrates]);

        // Therefore, Socrates is mortal
        let socrates_is_mortal = is_mortal.with(&[socrates]);

        let solution = Problem::new()
            .with_axiom(socrates_is_man)
            .with_axiom(men_are_mortal)
            .conjecture(socrates_is_mortal)
            .solve();

        assert_eq!(solution, ProofRes::Proved);
    }

    #[test]
    fn graph_reachability() {
        // Prove transitive reachability in a graph
        // Given: edge(a,b), edge(b,c), edge(c,d), edge(d,e)
        // And: path(x,y) if edge(x,y)
        // And: path is transitive: path(x,y) ∧ path(y,z) → path(x,z)
        // Prove: path(a,e)

        let edge = Predicate::new("edge", 2);
        let path = Predicate::new("path", 2);

        // Define nodes
        let a = Function::constant("a");
        let b = Function::constant("b");
        let c = Function::constant("c");
        let d = Function::constant("d");
        let e = Function::constant("e");

        // Axiom 1: Direct edges are paths
        // ∀x,y. edge(x,y) → path(x,y)
        let direct_edge_is_path = forall(|x| forall(|y| edge.with(&[x, y]) >> path.with(&[x, y])));

        // Axiom 2: Transitivity of paths
        // ∀x,y,z. path(x,y) ∧ path(y,z) → path(x,z)
        let path_transitivity = forall(|x| {
            forall(|y| forall(|z| (path.with(&[x, y]) & path.with(&[y, z])) >> path.with(&[x, z])))
        });

        // Concrete edges in the graph
        let edge_ab = edge.with(&[a, b]);
        let edge_bc = edge.with(&[b, c]);
        let edge_cd = edge.with(&[c, d]);
        let edge_de = edge.with(&[d, e]);

        // Conjecture: there is a path from a to e
        let conjecture = path.with(&[a, e]);

        let solution = Problem::new()
            .with_axiom(direct_edge_is_path)
            .with_axiom(path_transitivity)
            .with_axiom(edge_ab)
            .with_axiom(edge_bc)
            .with_axiom(edge_cd)
            .with_axiom(edge_de)
            .conjecture(conjecture)
            .solve();

        assert_eq!(solution, ProofRes::Proved);
    }

    #[test]
    fn group_left_identity() {
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
        let mul = |x: Term, y: Term| -> Term { mult.with(&[x, y]) };

        // Axiom 1: Right identity - ∀x. x * 1 = x
        let right_identity = forall(|x| mul(x, one).eq(x));

        // Axiom 2: Right inverse - ∀x. x * inv(x) = 1
        let right_inverse = forall(|x| {
            let inv_x = inv.with(&[x]);
            mul(x, inv_x).eq(one)
        });

        // Axiom 3: Associativity - ∀x,y,z. (x * y) * z = x * (y * z)
        let associativity =
            forall(|x| forall(|y| forall(|z| mul(mul(x, y), z).eq(mul(x, mul(y, z))))));

        // Conjecture: Left identity - ∀x. 1 * x = x
        let left_identity = forall(|x| mul(one, x).eq(x));

        let solution = Problem::new()
            .with_axiom(right_identity)
            .with_axiom(right_inverse)
            .with_axiom(associativity)
            .conjecture(left_identity)
            .solve();

        assert_eq!(solution, ProofRes::Proved);
    }

    #[test]
    fn group_index2_subgroup_normal() {
        // Prove that every subgroup of index 2 is normal.
        let mult = Function::new("mult", 2);
        let inv = Function::new("inv", 1);
        let one = Function::constant("1");

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
        let associativity =
            forall(|x| forall(|y| forall(|z| mul(mul(x, y), z).eq(mul(x, mul(y, z))))));

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

        let solution = Problem::new()
            .with_axiom(right_identity)
            .with_axiom(right_inverse)
            .with_axiom(associativity)
            .with_axiom(h_ident)
            .with_axiom(h_mul_closed)
            .with_axiom(h_inv_closed)
            .with_axiom(h_index_2)
            .conjecture(h_normal)
            .solve();

        assert_eq!(solution, ProofRes::Proved);
    }
}
