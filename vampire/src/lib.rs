use crate::lock::synced;
use std::{
    ffi::CString,
    ops::{BitAnd, BitOr, Shr},
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

    pub fn not(&self) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_not(self.id) };
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

impl Shr for Formula {
    type Output = Formula;

    fn shr(self, rhs: Self) -> Self::Output {
        self.imp(rhs)
    }
}

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
    use crate::{Function, Predicate, Problem, forall};

    #[test]
    fn socrates() {
        let is_mortal = Predicate::new("mortal", 1);
        let is_man = Predicate::new("man", 1);

        let men_are_mortal = forall(|x| is_man.with(&[x]) >> is_mortal.with(&[x]));

        let socrates = Function::constant("socrates");
        let socrates_is_man = is_man.with(&[socrates]);
        let socrates_is_mortal = is_mortal.with(&[socrates]);

        let solution = Problem::new()
            .with_axiom(socrates_is_man)
            .with_axiom(men_are_mortal)
            .conjecture(socrates_is_mortal)
            .solve();

        dbg!(solution);
        assert!(false);
    }
}
