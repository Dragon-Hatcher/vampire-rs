//! A Rust interface to the Vampire theorem prover.
//!
//! This crate provides safe Rust bindings to Vampire, a state-of-the-art automated
//! theorem prover for first-order logic with equality. Vampire can prove theorems,
//! check satisfiability, and find counterexamples in various mathematical domains.
//!
//! # Thread Safety
//!
//! **Important**: The underlying Vampire library is not thread-safe. This crate
//! protects all operations with a global mutex, so while you can safely use the
//! library from multiple threads, all proof operations will be serialized. Only
//! one proof can execute at a time.
//!
//! # Quick Start
//!
//! ```
//! use vampire_prover::{Function, Predicate, Problem, ProofRes, Options, forall};
//!
//! // Create predicates
//! let is_mortal = Predicate::new("mortal", 1);
//! let is_man = Predicate::new("man", 1);
//!
//! // Create a universal statement: ∀x. man(x) → mortal(x)
//! let men_are_mortal = forall(|x| is_man.with(x) >> is_mortal.with(x));
//!
//! // Create a constant
//! let socrates = Function::constant("socrates");
//!
//! // Build and solve the problem
//! let result = Problem::new(Options::new())
//!     .with_axiom(is_man.with(socrates))    // Socrates is a man
//!     .with_axiom(men_are_mortal)              // All men are mortal
//!     .conjecture(is_mortal.with(socrates)) // Therefore, Socrates is mortal
//!     .solve();
//!
//! assert_eq!(result, ProofRes::Proved);
//! ```
//!
//! # Core Concepts
//!
//! ## Terms
//!
//! Terms represent objects in first-order logic. They can be:
//! - **Constants**: Nullary functions like `socrates`
//! - **Variables**: Bound or free variables like `x` in `∀x. P(x)`
//! - **Function applications**: e.g., `mult(x, y)`
//!
//! ## Formulas
//!
//! Formulas are logical statements that can be:
//! - **Predicates**: `mortal(socrates)`
//! - **Equality**: `x = y`
//! - **Logical connectives**: `P ∧ Q`, `P ∨ Q`, `P → Q`, `P ↔ Q`, `¬P`
//! - **Quantifiers**: `∀x. P(x)`, `∃x. P(x)`
//!
//! ## Operators
//!
//! The crate provides Rust operators for logical connectives:
//! - `&` for conjunction (AND)
//! - `|` for disjunction (OR)
//! - `>>` for implication
//! - `!` for negation (NOT)
//! - [`Formula::iff`] for biconditional (if and only if)
//!
//! # Examples
//!
//! ## Graph Reachability
//!
//! Prove transitivity of paths in a graph:
//!
//! ```
//! use vampire_prover::{Function, Predicate, Problem, ProofRes, Options, forall};
//!
//! let edge = Predicate::new("edge", 2);
//! let path = Predicate::new("path", 2);
//!
//! // Create nodes
//! let a = Function::constant("a");
//! let b = Function::constant("b");
//! let c = Function::constant("c");
//!
//! // Axiom: edges are paths
//! let edges_are_paths = forall(|x| forall(|y|
//!     edge.with([x, y]) >> path.with([x, y])
//! ));
//!
//! // Axiom: paths are transitive
//! let transitivity = forall(|x| forall(|y| forall(|z|
//!     (path.with([x, y]) & path.with([y, z])) >> path.with([x, z])
//! )));
//!
//! let result = Problem::new(Options::new())
//!     .with_axiom(edges_are_paths)
//!     .with_axiom(transitivity)
//!     .with_axiom(edge.with([a, b]))
//!     .with_axiom(edge.with([b, c]))
//!     .conjecture(path.with([a, c]))
//!     .solve();
//!
//! assert_eq!(result, ProofRes::Proved);
//! ```
//!
//! ## Group Theory
//!
//! Prove that left identity follows from the standard group axioms:
//!
//! ```
//! use vampire_prover::{Function, Problem, ProofRes, Options, Term, forall};
//!
//! let mult = Function::new("mult", 2);
//! let inv = Function::new("inv", 1);
//! let one = Function::constant("1");
//!
//! let mul = |x: Term, y: Term| mult.with([x, y]);
//!
//! // Group Axiom 1: Right identity - ∀x. x * 1 = x
//! let right_identity = forall(|x| mul(x, one).eq(x));
//!
//! // Group Axiom 2: Right inverse - ∀x. x * inv(x) = 1
//! let right_inverse = forall(|x| {
//!     let inv_x = inv.with(x);
//!     mul(x, inv_x).eq(one)
//! });
//!
//! // Group Axiom 3: Associativity - ∀x,y,z. (x * y) * z = x * (y * z)
//! let associativity = forall(|x| forall(|y| forall(|z|
//!     mul(mul(x, y), z).eq(mul(x, mul(y, z)))
//! )));
//!
//! // Prove left identity: ∀x. 1 * x = x
//! let left_identity = forall(|x| mul(one, x).eq(x));
//!
//! let result = Problem::new(Options::new())
//!     .with_axiom(right_identity)
//!     .with_axiom(right_inverse)
//!     .with_axiom(associativity)
//!     .conjecture(left_identity)
//!     .solve();
//!
//! assert_eq!(result, ProofRes::Proved);
//! ```
//!
//! # License
//!
//! This Rust crate is dual-licensed under MIT OR Apache-2.0 (your choice).
//!
//! The underlying Vampire theorem prover is licensed under the BSD 3-Clause License.
//! When distributing applications using this crate, you must comply with both
//! licenses. See the [Vampire LICENCE](https://github.com/vprover/vampire/blob/master/LICENCE)
//! for details on the Vampire license requirements.

use crate::lock::synced;
use std::{
    ffi::CString,
    ops::{BitAnd, BitOr, Not, Shr},
    time::Duration,
};
use vampire_sys as sys;

mod lock;

/// Trait for types that can be converted into term arguments.
///
/// This trait allows `.with()` methods on [`Function`] and [`Predicate`] to accept
/// different argument formats for convenience:
/// - Single term: `f.with(x)`
/// - Array: `f.with([x, y])`
pub trait IntoTermArgs {
    /// Convert this type into a slice of terms.
    fn as_slice(&self) -> &[Term];
}

impl IntoTermArgs for Term {
    fn as_slice(&self) -> &[Term] {
        std::slice::from_ref(self)
    }
}

impl<T> IntoTermArgs for T
where
    T: AsRef<[Term]>,
{
    fn as_slice(&self) -> &[Term] {
        self.as_ref()
    }
}

/// A function symbol in first-order logic.
///
/// Functions represent operations that take terms as arguments and produce new terms.
/// They have a fixed arity (number of arguments). A function with arity 0 is called a
/// constant and represents a specific object in the domain.
///
/// # Examples
///
/// ```
/// use vampire_prover::Function;
///
/// // Create a constant (0-ary function)
/// let socrates = Function::constant("socrates");
///
/// // Create a unary function
/// let successor = Function::new("succ", 1);
///
/// // Create a binary function
/// let add = Function::new("add", 2);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Function {
    id: u32,
    arity: u32,
}

impl Function {
    /// Creates a new function symbol with the given name and arity.
    ///
    /// Calling this method multiple times with the same name and arity will return
    /// the same function symbol. It is safe to call this with the same name but
    /// different arities - they will be treated as distinct function symbols.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the function symbol
    /// * `arity` - The number of arguments this function takes
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Function;
    ///
    /// let mult = Function::new("mult", 2);
    /// assert_eq!(mult.arity(), 2);
    ///
    /// // Same name and arity returns the same symbol
    /// let mult2 = Function::new("mult", 2);
    /// assert_eq!(mult, mult2);
    ///
    /// // Same name but different arity is a different symbol
    /// let mult3 = Function::new("mult", 3);
    /// assert_ne!(mult.arity(), mult3.arity());
    /// ```
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

    /// Returns the arity (number of arguments) of this function.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Function;
    ///
    /// let f = Function::new("f", 3);
    /// assert_eq!(f.arity(), 3);
    /// ```
    pub fn arity(&self) -> u32 {
        self.arity
    }

    /// Creates a constant term (0-ary function).
    ///
    /// This is a convenience method equivalent to `Function::new(name, 0).with([])`.
    /// Constants represent specific objects in the domain.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the constant
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Function;
    ///
    /// let socrates = Function::constant("socrates");
    /// let zero = Function::constant("0");
    /// ```
    pub fn constant(name: &str) -> Term {
        Self::new(name, 0).with([])
    }

    /// Applies this function to the given arguments, creating a term.
    ///
    /// This method accepts multiple argument formats for convenience:
    /// - Single term: `f.with(x)`
    /// - Array: `f.with([x, y])`
    ///
    /// # Panics
    ///
    /// Panics if the number of arguments does not match the function's arity.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Term};
    ///
    /// let add = Function::new("add", 2);
    /// let x = Term::new_var(0);
    /// let y = Term::new_var(1);
    ///
    /// // Multiple arguments:
    /// let sum = add.with([x, y]);
    ///
    /// // Single argument:
    /// let succ = Function::new("succ", 1);
    /// let sx = succ.with(x);
    /// ```
    pub fn with(&self, args: impl IntoTermArgs) -> Term {
        Term::new_function(*self, args.as_slice())
    }
}

/// A predicate symbol in first-order logic.
///
/// Predicates represent relations or properties that can be true or false.
/// They take terms as arguments and produce formulas. Like functions, predicates
/// have a fixed arity.
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate};
///
/// // Unary predicate (property)
/// let is_mortal = Predicate::new("mortal", 1);
/// let socrates = Function::constant("socrates");
/// let formula = is_mortal.with(socrates); // mortal(socrates)
///
/// // Binary predicate (relation)
/// let loves = Predicate::new("loves", 2);
/// let alice = Function::constant("alice");
/// let bob = Function::constant("bob");
/// let formula = loves.with([alice, bob]); // loves(alice, bob)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Predicate {
    id: u32,
    arity: u32,
}

impl Predicate {
    /// Creates a new predicate symbol with the given name and arity.
    ///
    /// Calling this method multiple times with the same name and arity will return
    /// the same predicate symbol. It is safe to call this with the same name but
    /// different arities - they will be treated as distinct predicate symbols.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the predicate symbol
    /// * `arity` - The number of arguments this predicate takes
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Predicate;
    ///
    /// let edge = Predicate::new("edge", 2);
    /// assert_eq!(edge.arity(), 2);
    ///
    /// // Same name and arity returns the same symbol
    /// let edge2 = Predicate::new("edge", 2);
    /// assert_eq!(edge, edge2);
    ///
    /// // Same name but different arity is a different symbol
    /// let edge3 = Predicate::new("edge", 3);
    /// assert_ne!(edge.arity(), edge3.arity());
    /// ```
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

    /// Returns the arity (number of arguments) of this predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Predicate;
    ///
    /// let p = Predicate::new("p", 2);
    /// assert_eq!(p.arity(), 2);
    /// ```
    pub fn arity(&self) -> u32 {
        self.arity
    }

    /// Applies this predicate to the given arguments, creating a formula.
    ///
    /// This method accepts multiple argument formats for convenience:
    /// - Single term: `p.with(x)`
    /// - Array: `p.with([x, y])`
    ///
    /// # Panics
    ///
    /// Panics if the number of arguments does not match the predicate's arity.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate};
    ///
    /// let mortal = Predicate::new("mortal", 1);
    /// let socrates = Function::constant("socrates");
    ///
    /// // Single argument:
    /// let formula = mortal.with(socrates);
    ///
    /// // Multiple arguments:
    /// let edge = Predicate::new("edge", 2);
    /// let a = Function::constant("a");
    /// let b = Function::constant("b");
    /// let e = edge.with([a, b]);
    /// ```
    pub fn with(&self, args: impl IntoTermArgs) -> Formula {
        Formula::new_predicate(*self, args.as_slice())
    }
}

/// A term in first-order logic.
///
/// Terms represent objects in the domain of discourse. A term can be:
/// - A constant: `socrates`
/// - A variable: `x`
/// - A function application: `add(x, y)`
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Term};
///
/// // Create a constant
/// let zero = Function::constant("0");
///
/// // Create a variable
/// let x = Term::new_var(0);
///
/// // Create a function application
/// let succ = Function::new("succ", 1);
/// let one = succ.with(zero);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Term {
    id: *mut sys::vampire_term_t,
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Term({})", self.to_string())
    }
}

impl Term {
    /// Converts this term to a string representation.
    ///
    /// # Panics
    ///
    /// Panics if the underlying C API fails (which should never happen in normal use).
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Function;
    ///
    /// let x = Function::constant("x");
    /// println!("{}", x.to_string()); // Prints the vampire string representation
    /// ```
    pub fn to_string(&self) -> String {
        synced(|_| unsafe {
            let ptr = sys::vampire_term_to_string(self.id);
            assert!(!ptr.is_null(), "vampire_term_to_string returned null");

            let c_str = std::ffi::CStr::from_ptr(ptr);
            let result = c_str
                .to_str()
                .expect("vampire returned invalid UTF-8")
                .to_string();
            sys::vampire_free_string(ptr);
            result
        })
    }

    /// Creates a term by applying a function to arguments.
    ///
    /// This is typically called via [`Function::with`] rather than directly.
    ///
    /// # Panics
    ///
    /// Panics if the number of arguments does not match the function's arity.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Term};
    ///
    /// let add = Function::new("add", 2);
    /// let x = Term::new_var(0);
    /// let y = Term::new_var(1);
    ///
    /// let sum = Term::new_function(add, &[x, y]);
    /// ```
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

    /// Creates a variable with the given index.
    ///
    /// Variables are typically used within quantified formulas. The index should be
    /// unique within a formula. For automatic variable management, consider using
    /// the [`forall`] and [`exists`] helper functions instead.
    ///
    /// # Arguments
    ///
    /// * `idx` - The unique index for this variable
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Term;
    ///
    /// let x = Term::new_var(0);
    /// let y = Term::new_var(1);
    /// ```
    pub fn new_var(idx: u32) -> Self {
        synced(|info| unsafe {
            info.free_var = info.free_var.max(idx + 1);
            let term = sys::vampire_var(idx);
            Self { id: term }
        })
    }

    /// Creates a fresh variable with an automatically assigned index.
    ///
    /// Returns both the variable term and its index. This is primarily used internally
    /// by the [`forall`] and [`exists`] functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Term;
    ///
    /// let (x, idx) = Term::free_var();
    /// assert_eq!(idx, 0);
    ///
    /// let (y, idx2) = Term::free_var();
    /// assert_eq!(idx2, 1);
    /// ```
    pub fn free_var() -> (Self, u32) {
        synced(|info| unsafe {
            let idx = info.free_var;
            info.free_var += 1;
            let term = sys::vampire_var(idx);
            (Self { id: term }, idx)
        })
    }

    /// Creates an equality formula between this term and another.
    ///
    /// # Arguments
    ///
    /// * `rhs` - The right-hand side of the equality
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, forall};
    ///
    /// let succ = Function::new("succ", 1);
    /// let zero = Function::constant("0");
    ///
    /// // ∀x. succ(x) = succ(x)
    /// let reflexive = forall(|x| {
    ///     let sx = succ.with(x);
    ///     sx.eq(sx)
    /// });
    /// ```
    pub fn eq(&self, rhs: Term) -> Formula {
        Formula::new_eq(*self, rhs)
    }
}

/// A formula in first-order logic.
///
/// Formulas are logical statements that can be true or false. They include:
/// - Atomic formulas: predicates and equalities
/// - Logical connectives: AND (`&`), OR (`|`), NOT (`!`), implication (`>>`), biconditional
/// - Quantifiers: universal (`∀`) and existential (`∃`)
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate, forall};
///
/// let p = Predicate::new("P", 1);
/// let q = Predicate::new("Q", 1);
/// let x = Function::constant("x");
///
/// // Atomic formula
/// let px = p.with(x);
/// let qx = q.with(x);
///
/// // Conjunction: P(x) ∧ Q(x)
/// let both = px & qx;
///
/// // Disjunction: P(x) ∨ Q(x)
/// let either = px | qx;
///
/// // Implication: P(x) → Q(x)
/// let implies = px >> qx;
///
/// // Negation: ¬P(x)
/// let not_px = !px;
///
/// // Universal quantification: ∀x. P(x)
/// let all = forall(|x| p.with(x));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Formula {
    id: *mut sys::vampire_formula_t,
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Formula({})", self.to_string())
    }
}

impl Formula {
    /// Converts this formula to a string representation.
    ///
    /// # Panics
    ///
    /// Panics if the underlying C API fails (which should never happen in normal use).
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate};
    ///
    /// let p = Predicate::new("P", 1);
    /// let x = Function::constant("x");
    /// let formula = p.with(x);
    /// println!("{}", formula.to_string()); // Prints the vampire string representation
    /// ```
    pub fn to_string(&self) -> String {
        synced(|_| unsafe {
            let ptr = sys::vampire_formula_to_string(self.id);
            assert!(!ptr.is_null(), "vampire_formula_to_string returned null");

            let c_str = std::ffi::CStr::from_ptr(ptr);
            let result = c_str
                .to_str()
                .expect("vampire returned invalid UTF-8")
                .to_string();
            sys::vampire_free_string(ptr);
            result
        })
    }

    /// Creates an atomic formula by applying a predicate to arguments.
    ///
    /// This is typically called via [`Predicate::with`] rather than directly.
    ///
    /// # Panics
    ///
    /// Panics if the number of arguments does not match the predicate's arity.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Formula};
    ///
    /// let mortal = Predicate::new("mortal", 1);
    /// let socrates = Function::constant("socrates");
    ///
    /// let formula = Formula::new_predicate(mortal, &[socrates]);
    /// ```
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

    /// Creates an equality formula between two terms.
    ///
    /// This is typically called via [`Term::eq`] rather than directly.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Formula};
    ///
    /// let x = Function::constant("x");
    /// let y = Function::constant("y");
    ///
    /// let eq = Formula::new_eq(x, y);
    /// ```
    pub fn new_eq(lhs: Term, rhs: Term) -> Self {
        synced(|_| unsafe {
            let lit = sys::vampire_eq(true, lhs.id, rhs.id);
            let atom = sys::vampire_atom(lit);
            Self { id: atom }
        })
    }

    /// Creates a conjunction (AND) of multiple formulas.
    ///
    /// For two formulas, the `&` operator is more convenient.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Formula};
    ///
    /// let p = Predicate::new("P", 1);
    /// let q = Predicate::new("Q", 1);
    /// let r = Predicate::new("R", 1);
    /// let x = Function::constant("x");
    ///
    /// // P(x) ∧ Q(x) ∧ R(x)
    /// let all_three = Formula::new_and(&[
    ///     p.with(x),
    ///     q.with(x),
    ///     r.with(x),
    /// ]);
    /// ```
    pub fn new_and(formulas: &[Formula]) -> Self {
        synced(|_| unsafe {
            let formula_count = formulas.len();
            let formulas = std::mem::transmute(formulas.as_ptr());
            let id = sys::vampire_and(formulas, formula_count);
            Self { id }
        })
    }

    /// Creates a disjunction (OR) of multiple formulas.
    ///
    /// For two formulas, the `|` operator is more convenient.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Formula};
    ///
    /// let p = Predicate::new("P", 1);
    /// let q = Predicate::new("Q", 1);
    /// let r = Predicate::new("R", 1);
    /// let x = Function::constant("x");
    ///
    /// // P(x) ∨ Q(x) ∨ R(x)
    /// let any = Formula::new_or(&[
    ///     p.with(x),
    ///     q.with(x),
    ///     r.with(x),
    /// ]);
    /// ```
    pub fn new_or(formulas: &[Formula]) -> Self {
        synced(|_| unsafe {
            let formula_count = formulas.len();
            let formulas = std::mem::transmute(formulas.as_ptr());
            let id = sys::vampire_or(formulas, formula_count);
            Self { id }
        })
    }

    /// Creates a negation (NOT) of a formula.
    ///
    /// The `!` operator is more convenient than calling this directly.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Formula};
    ///
    /// let p = Predicate::new("P", 1);
    /// let x = Function::constant("x");
    ///
    /// let not_p = Formula::new_not(p.with(x));
    /// ```
    pub fn new_not(formula: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_not(formula.id) };
            Self { id }
        })
    }

    /// Creates a universally quantified formula.
    ///
    /// The [`forall`] helper function provides a more ergonomic interface.
    ///
    /// # Arguments
    ///
    /// * `var` - The index of the variable to quantify
    /// * `f` - The formula body
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Formula, Term};
    ///
    /// let p = Predicate::new("P", 1);
    /// let x = Term::new_var(0);
    ///
    /// // ∀x. P(x)
    /// let all_p = Formula::new_forall(0, p.with(x));
    /// ```
    pub fn new_forall(var: u32, f: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_forall(var, f.id) };
            Self { id }
        })
    }

    /// Creates an existentially quantified formula.
    ///
    /// The [`exists`] helper function provides a more ergonomic interface.
    ///
    /// # Arguments
    ///
    /// * `var` - The index of the variable to quantify
    /// * `f` - The formula body
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Formula, Term};
    ///
    /// let p = Predicate::new("P", 1);
    /// let x = Term::new_var(0);
    ///
    /// // ∃x. P(x)
    /// let some_p = Formula::new_exists(0, p.with(x));
    /// ```
    pub fn new_exists(var: u32, f: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_exists(var, f.id) };
            Self { id }
        })
    }

    /// Creates an implication from this formula to another.
    ///
    /// The `>>` operator is more convenient than calling this directly.
    ///
    /// # Arguments
    ///
    /// * `rhs` - The consequent (right-hand side) of the implication
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate};
    ///
    /// let p = Predicate::new("P", 1);
    /// let q = Predicate::new("Q", 1);
    /// let x = Function::constant("x");
    ///
    /// // P(x) → Q(x)
    /// let implication = p.with(x).imp(q.with(x));
    /// ```
    pub fn imp(&self, rhs: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_imp(self.id, rhs.id) };
            Self { id }
        })
    }

    /// Creates a biconditional (if and only if) between this formula and another.
    ///
    /// A biconditional `P ↔ Q` is true when both formulas have the same truth value.
    ///
    /// # Arguments
    ///
    /// * `rhs` - The right-hand side of the biconditional
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, forall};
    ///
    /// let even = Predicate::new("even", 1);
    /// let div_by_2 = Predicate::new("divisible_by_2", 1);
    ///
    /// // ∀x. even(x) ↔ divisible_by_2(x)
    /// let equiv = forall(|x| {
    ///     even.with(x).iff(div_by_2.with(x))
    /// });
    /// ```
    pub fn iff(&self, rhs: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_iff(self.id, rhs.id) };
            Self { id }
        })
    }
}

/// Creates a universally quantified formula using a closure.
///
/// This is the most ergonomic way to create formulas with universal quantification.
/// The closure receives a fresh variable term that can be used in the formula body.
///
/// # Arguments
///
/// * `f` - A closure that takes a [`Term`] representing the quantified variable and
///         returns a [`Formula`]
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate, forall};
///
/// let p = Predicate::new("P", 1);
///
/// // ∀x. P(x)
/// let all_p = forall(|x| p.with(x));
///
/// // Nested quantifiers: ∀x. ∀y. P(x, y)
/// let p2 = Predicate::new("P", 2);
/// let all_xy = forall(|x| forall(|y| p2.with([x, y])));
/// ```
///
/// # Complex Example
///
/// ```
/// use vampire_prover::{Function, Predicate, forall};
///
/// let mortal = Predicate::new("mortal", 1);
/// let human = Predicate::new("human", 1);
///
/// // ∀x. human(x) → mortal(x)
/// let humans_are_mortal = forall(|x| {
///     human.with(x) >> mortal.with(x)
/// });
/// ```
pub fn forall<F: FnOnce(Term) -> Formula>(f: F) -> Formula {
    let (var, var_idx) = Term::free_var();
    let f = f(var);
    Formula::new_forall(var_idx, f)
}

/// Creates an existentially quantified formula using a closure.
///
/// This is the most ergonomic way to create formulas with existential quantification.
/// The closure receives a fresh variable term that can be used in the formula body.
///
/// # Arguments
///
/// * `f` - A closure that takes a [`Term`] representing the quantified variable and
///         returns a [`Formula`]
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate, exists};
///
/// let prime = Predicate::new("prime", 1);
///
/// // ∃x. prime(x) - "There exists a prime number"
/// let some_prime = exists(|x| prime.with(x));
///
/// // ∃x. ∃y. edge(x, y) - "There exists an edge"
/// let edge = Predicate::new("edge", 2);
/// let has_edge = exists(|x| exists(|y| edge.with([x, y])));
/// ```
///
/// # Complex Example
///
/// ```
/// use vampire_prover::{Function, Predicate, exists, forall};
///
/// let greater = Predicate::new("greater", 2);
///
/// // ∃x. ∀y. greater(x, y) - "There exists a maximum element"
/// let has_maximum = exists(|x| forall(|y| greater.with([x, y])));
/// ```
pub fn exists<F: FnOnce(Term) -> Formula>(f: F) -> Formula {
    let (var, var_idx) = Term::free_var();
    let f = f(var);
    Formula::new_exists(var_idx, f)
}

/// Implements the `&` operator for conjunction (AND).
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate};
///
/// let p = Predicate::new("P", 1);
/// let q = Predicate::new("Q", 1);
/// let x = Function::constant("x");
///
/// // P(x) ∧ Q(x)
/// let both = p.with(x) & q.with(x);
/// ```
impl BitAnd for Formula {
    type Output = Formula;

    fn bitand(self, rhs: Self) -> Self::Output {
        Formula::new_and(&[self, rhs])
    }
}

/// Implements the `|` operator for disjunction (OR).
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate};
///
/// let p = Predicate::new("P", 1);
/// let q = Predicate::new("Q", 1);
/// let x = Function::constant("x");
///
/// // P(x) ∨ Q(x)
/// let either = p.with(x) | q.with(x);
/// ```
impl BitOr for Formula {
    type Output = Formula;

    fn bitor(self, rhs: Self) -> Self::Output {
        Formula::new_or(&[self, rhs])
    }
}

/// Implements the `!` operator for negation (NOT).
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate};
///
/// let p = Predicate::new("P", 1);
/// let x = Function::constant("x");
///
/// // ¬P(x)
/// let not_p = !p.with(x);
/// ```
impl Not for Formula {
    type Output = Formula;

    fn not(self) -> Self::Output {
        Formula::new_not(self)
    }
}

/// Implements the `>>` operator for implication.
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate};
///
/// let p = Predicate::new("P", 1);
/// let q = Predicate::new("Q", 1);
/// let x = Function::constant("x");
///
/// // P(x) → Q(x)
/// let implies = p.with(x) >> q.with(x);
/// ```
impl Shr for Formula {
    type Output = Formula;

    fn shr(self, rhs: Self) -> Self::Output {
        self.imp(rhs)
    }
}

/// Configuration options for the Vampire theorem prover.
///
/// Options allow you to configure the behavior of the prover, such as setting
/// time limits. Use the builder pattern to construct options.
///
/// # Examples
///
/// ```
/// use vampire_prover::Options;
/// use std::time::Duration;
///
/// // Default options (no timeout)
/// let opts = Options::new();
///
/// // Set a timeout
/// let opts = Options::new().timeout(Duration::from_secs(5));
/// ```
#[derive(Debug, Clone)]
pub struct Options {
    timeout: Option<Duration>,
}

impl Options {
    /// Creates a new Options with default settings.
    ///
    /// By default, no timeout is set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Options;
    ///
    /// let opts = Options::new();
    /// ```
    pub fn new() -> Self {
        Self { timeout: None }
    }

    /// Sets the timeout for the prover.
    ///
    /// If the prover exceeds this time limit, it will return
    /// [`ProofRes::Unknown(UnknownReason::Timeout)`].
    ///
    /// # Arguments
    ///
    /// * `duration` - The maximum time the prover should run
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Options;
    /// use std::time::Duration;
    ///
    /// let opts = Options::new().timeout(Duration::from_secs(10));
    /// ```
    pub fn timeout(&mut self, duration: Duration) -> &mut Self {
        self.timeout = Some(duration);
        self
    }
}

impl Default for Options {
    fn default() -> Self {
        Self::new()
    }
}

/// A theorem proving problem consisting of axioms and an optional conjecture.
///
/// A [`Problem`] is constructed by adding axioms (assumed to be true) and optionally
/// a conjecture (the statement to be proved). The problem is then solved by calling
/// [`Problem::solve`], which invokes the Vampire theorem prover.
///
/// # Examples
///
/// ## Basic Usage
///
/// ```
/// use vampire_prover::{Function, Predicate, Problem, ProofRes, Options, forall};
///
/// let mortal = Predicate::new("mortal", 1);
/// let human = Predicate::new("human", 1);
/// let socrates = Function::constant("socrates");
///
/// let result = Problem::new(Options::new())
///     .with_axiom(human.with(socrates))
///     .with_axiom(forall(|x| human.with(x) >> mortal.with(x)))
///     .conjecture(mortal.with(socrates))
///     .solve();
///
/// assert_eq!(result, ProofRes::Proved);
/// ```
///
/// ## Without Conjecture
///
/// You can also create problems without a conjecture to check satisfiability:
///
/// ```
/// use vampire_prover::{Function, Predicate, Problem, Options};
///
/// let p = Predicate::new("P", 1);
/// let x = Function::constant("x");
///
/// let result = Problem::new(Options::new())
///     .with_axiom(p.with(x))
///     .with_axiom(!p.with(x))  // Contradiction
///     .solve();
///
/// // This should be unsatisfiable
/// ```
#[derive(Debug, Clone)]
pub struct Problem {
    options: Options,
    axioms: Vec<Formula>,
    conjecture: Option<Formula>,
}

impl Problem {
    /// Creates a new empty problem with the given options.
    ///
    /// # Arguments
    ///
    /// * `options` - Configuration options for the prover
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Problem, Options};
    /// use std::time::Duration;
    ///
    /// // Default options
    /// let problem = Problem::new(Options::new());
    /// ```
    pub fn new(options: Options) -> Self {
        Self {
            options,
            axioms: Vec::new(),
            conjecture: None,
        }
    }

    /// Adds an axiom to the problem.
    ///
    /// Axioms are formulas assumed to be true. The prover will use these axioms
    /// to attempt to prove the conjecture (if one is provided).
    ///
    /// This method consumes `self` and returns a new [`Problem`], allowing for
    /// method chaining.
    ///
    /// # Arguments
    ///
    /// * `f` - The axiom formula to add
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Problem, Options, forall};
    ///
    /// let p = Predicate::new("P", 1);
    /// let q = Predicate::new("Q", 1);
    ///
    /// let problem = Problem::new(Options::new())
    ///     .with_axiom(forall(|x| p.with(x)))
    ///     .with_axiom(forall(|x| p.with(x) >> q.with(x)));
    /// ```
    pub fn with_axiom(&mut self, f: Formula) -> &mut Self {
        self.axioms.push(f);
        self
    }

    /// Sets the conjecture for the problem.
    ///
    /// The conjecture is the statement that the prover will attempt to prove from
    /// the axioms. A problem can have at most one conjecture.
    ///
    /// This method consumes `self` and returns a new [`Problem`], allowing for
    /// method chaining.
    ///
    /// # Arguments
    ///
    /// * `f` - The conjecture formula
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Problem, Options, forall};
    ///
    /// let p = Predicate::new("P", 1);
    /// let q = Predicate::new("Q", 1);
    ///
    /// let problem = Problem::new(Options::new())
    ///     .with_axiom(forall(|x| p.with(x) >> q.with(x)))
    ///     .conjecture(forall(|x| q.with(x)));  // Try to prove this
    /// ```
    pub fn conjecture(&mut self, f: Formula) -> &mut Self {
        self.conjecture = Some(f);
        self
    }

    /// Solves the problem using the Vampire theorem prover.
    ///
    /// This method consumes the problem and invokes Vampire to either prove the
    /// conjecture from the axioms, find a counterexample, or determine that the
    /// result is unknown.
    ///
    /// # Returns
    ///
    /// A [`ProofRes`] indicating whether the conjecture was proved, found to be
    /// unprovable, or whether the result is unknown (due to timeout, memory limits,
    /// or incompleteness).
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::{Function, Predicate, Problem, ProofRes, Options, forall};
    ///
    /// let p = Predicate::new("P", 1);
    /// let x = Function::constant("x");
    ///
    /// let result = Problem::new(Options::new())
    ///     .with_axiom(p.with(x))
    ///     .conjecture(p.with(x))
    ///     .solve();
    ///
    /// assert_eq!(result, ProofRes::Proved);
    /// ```
    pub fn solve(&mut self) -> ProofRes {
        synced(|_| unsafe {
            sys::vampire_prepare_for_next_proof();

            // Apply timeout option if set
            if let Some(timeout) = self.options.timeout {
                let ms = timeout.as_millis().max(1);
                sys::vampire_set_time_limit_milliseconds(ms as i32);
            }

            let mut units = Vec::new();

            for axiom in &self.axioms {
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

/// The result of attempting to prove a theorem.
///
/// After calling [`Problem::solve`], Vampire returns one of three possible results:
/// - [`ProofRes::Proved`]: The conjecture was successfully proved from the axioms
/// - [`ProofRes::Unprovable`]: The axioms are insufficient to prove the conjecture
/// - [`ProofRes::Unknown`]: Vampire could not determine if the axioms imply the conjecture
///
/// # Examples
///
/// ```
/// use vampire_prover::{Function, Predicate, Problem, ProofRes, Options, forall};
///
/// let p = Predicate::new("P", 1);
/// let x = Function::constant("x");
///
/// let result = Problem::new(Options::new())
///     .with_axiom(p.with(x))
///     .conjecture(p.with(x))
///     .solve();
///
/// match result {
///     ProofRes::Proved => println!("Theorem proved!"),
///     ProofRes::Unprovable => println!("Counterexample found"),
///     ProofRes::Unknown(reason) => println!("Unknown: {:?}", reason),
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofRes {
    /// The conjecture was successfully proved from the axioms.
    Proved,

    /// The axioms are insufficient to prove the conjecture.
    ///
    /// Vampire has determined that the given axioms do not imply the conjecture.
    /// Note that this does not mean the conjecture is false - it could still be
    /// true or false, but the provided axioms alone cannot establish it.
    Unprovable,

    /// Vampire could not determine whether the axioms imply the conjecture.
    ///
    /// This can happen for several reasons, detailed in [`UnknownReason`].
    Unknown(UnknownReason),
}

/// The reason why a proof result is unknown.
///
/// When Vampire cannot determine whether a conjecture is provable, it returns
/// [`ProofRes::Unknown`] with one of these reasons.
///
/// # Examples
///
/// ```
/// use vampire_prover::{ProofRes, UnknownReason};
///
/// let result = ProofRes::Unknown(UnknownReason::Timeout);
///
/// if let ProofRes::Unknown(reason) = result {
///     match reason {
///         UnknownReason::Timeout => println!("Ran out of time"),
///         UnknownReason::MemoryLimit => println!("Ran out of memory"),
///         UnknownReason::Incomplete => println!("Problem uses incomplete logic"),
///         UnknownReason::Unknown => println!("Unknown reason"),
///     }
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnknownReason {
    /// The prover exceeded its time limit before finding a proof or counterexample.
    Timeout,

    /// The prover exceeded its memory limit before finding a proof or counterexample.
    MemoryLimit,

    /// The problem involves features that make the logic incomplete.
    ///
    /// Some logical theories (e.g., higher-order logic, certain arithmetic theories)
    /// are undecidable, meaning no algorithm can always find an answer.
    Incomplete,

    /// The reason is unknown or not specified by Vampire.
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
    use crate::{Function, Options, Predicate, Problem, ProofRes, Term, exists, forall};

    #[test]
    fn test_with_syntax() {
        // Test that all three calling styles work
        let f = Function::new("f", 2);
        let p = Predicate::new("p", 1);
        let x = Term::new_var(0);
        let y = Term::new_var(1);

        // Test arrays
        let _t1 = f.with([x, y]);
        let _f1 = p.with([x]);

        // Test slice references
        let _t2 = f.with(&[x, y]);
        let _f2 = p.with(&[x]);

        let _t3 = f.with(&vec![x, y]);
        let _f3 = p.with(vec![x]);

        // Test single term
        let _f4 = p.with(x);
    }

    #[test]
    fn socrates_proof() {
        // Classic Socrates syllogism
        let is_mortal = Predicate::new("mortal", 1);
        let is_man = Predicate::new("man", 1);

        // All men are mortal
        let men_are_mortal = forall(|x| is_man.with(x) >> is_mortal.with(x));

        // Socrates is a man
        let socrates = Function::constant("socrates");
        let socrates_is_man = is_man.with(socrates);

        // Therefore, Socrates is mortal
        let socrates_is_mortal = is_mortal.with(socrates);

        let solution = Problem::new(Options::new())
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
        let direct_edge_is_path = forall(|x| forall(|y| edge.with([x, y]) >> path.with([x, y])));

        // Axiom 2: Transitivity of paths
        // ∀x,y,z. path(x,y) ∧ path(y,z) → path(x,z)
        let path_transitivity = forall(|x| {
            forall(|y| forall(|z| (path.with([x, y]) & path.with([y, z])) >> path.with([x, z])))
        });

        // Concrete edges in the graph
        let edge_ab = edge.with([a, b]);
        let edge_bc = edge.with([b, c]);
        let edge_cd = edge.with([c, d]);
        let edge_de = edge.with([d, e]);

        // Conjecture: there is a path from a to e
        let conjecture = path.with([a, e]);

        let solution = Problem::new(Options::new())
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
        let mul = |x: Term, y: Term| -> Term { mult.with([x, y]) };

        // Axiom 1: Right identity - ∀x. x * 1 = x
        let right_identity = forall(|x| mul(x, one).eq(x));

        // Axiom 2: Right inverse - ∀x. x * inv(x) = 1
        let right_inverse = forall(|x| {
            let inv_x = inv.with(x);
            mul(x, inv_x).eq(one)
        });

        // Axiom 3: Associativity - ∀x,y,z. (x * y) * z = x * (y * z)
        let associativity =
            forall(|x| forall(|y| forall(|z| mul(mul(x, y), z).eq(mul(x, mul(y, z))))));

        // Conjecture: Left identity - ∀x. 1 * x = x
        let left_identity = forall(|x| mul(one, x).eq(x));

        let solution = Problem::new(Options::new())
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
        let mul = |x: Term, y: Term| -> Term { mult.with([x, y]) };

        // Group Axiom 1: Right identity - ∀x. x * 1 = x
        let right_identity = forall(|x| mul(x, one).eq(x));

        // Group Axiom 2: Right inverse - ∀x. x * inv(x) = 1
        let right_inverse = forall(|x| {
            let inv_x = inv.with(x);
            mul(x, inv_x).eq(one)
        });

        // Group Axiom 3: Associativity - ∀x,y,z. (x * y) * z = x * (y * z)
        let associativity =
            forall(|x| forall(|y| forall(|z| mul(mul(x, y), z).eq(mul(x, mul(y, z))))));

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

        let solution = Problem::new(Options::new())
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
