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
//! ```ignore
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
//! ```ignore
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
//! ```ignore
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

// This crate is a pure FFI shell over the C++ Vampire prover. The pure-Rust
// IR types (`Formula`, `Term`, `Sort`, `Function`, `Predicate`, `Problem`,
// `Interp`, `VarId`, `LogicMode`) live in `sigmakee-rs-core::trans::ir`,
// which is the canonical home for problem construction and TPTP
// serialisation.
//
// Modules:
//
// * `options` — `Options` (timeout + extra Vampire options). Pure data,
//   no C++ dependency. Available without the `integrated-prover` feature.
//
// * `ffi` — the FFI-backed types that link the Vampire C++ library. Only
//   compiled when the `integrated-prover` feature is enabled (default on).
//   Its types are re-exported at the crate root with a `Sys` prefix
//   (`SysFormula`, `SysTerm`, `SysSort`, `SysFunction`, `SysPredicate`,
//   `SysProblem`, `SysInterp`). Proof-result types and DSL helpers keep
//   their original names since they have no IR counterpart.
//
// * `lock` — global Vampire mutex for serialising FFI calls.

pub mod options;
pub use options::Options;

#[cfg(feature = "integrated-prover")]
pub mod lock;

#[cfg(feature = "integrated-prover")]
pub mod ffi;

// FFI-backed solve types: renamed with `Sys` prefix at the crate root.
#[cfg(feature = "integrated-prover")]
pub use ffi::{
    Formula   as SysFormula,
    Function  as SysFunction,
    Interp    as SysInterp,
    Predicate as SysPredicate,
    Problem   as SysProblem,
    Sort      as SysSort,
    Term      as SysTerm,
};

// Solve results + DSL helpers have no IR counterparts; keep their names.
#[cfg(feature = "integrated-prover")]
pub use ffi::{
    exists, exists_typed, forall, forall_typed, IntoTerm, IntoTermArgs,
    Proof, ProofRes, ProofRule, ProofStep, UnknownReason,
};
