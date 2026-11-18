# vampire

Safe Rust bindings to the [Vampire](https://vprover.github.io/) theorem prover for first-order logic with equality.

## Overview

This crate provides a high-level, safe Rust interface to Vampire, a state-of-the-art automated theorem prover. Vampire can prove theorems, check satisfiability, and find counterexamples in various mathematical domains including:

- Propositional and first-order logic
- **Typed First-Order Form (TFF)** support
- **Interpreted Arithmetic** (Integers, Rationals, Reals)
- Equality reasoning and Group theory
- Graph properties and Program verification
- **CNF Clausification** (extracting clauses from formulas)

## Quick Start

```rust
use vampire_prover::{Function, Predicate, Problem, ProofRes, Options, forall};

// Create predicates
let is_mortal = Predicate::new("mortal", 1);
let is_man = Predicate::new("man", 1);

// Create a universal statement: ∀x. man(x) → mortal(x)
let men_are_mortal = forall(|x| is_man.with(x) >> is_mortal.with(x));

// Create a constant
let socrates = Function::constant("socrates");

// Build and solve the problem
let result = Problem::new(Options::new())
    .with_axiom(is_man.with(socrates))       // Socrates is a man
    .with_axiom(men_are_mortal)              // All men are mortal
    .conjecture(is_mortal.with(socrates))    // Therefore, Socrates is mortal
    .solve();

assert_eq!(result, ProofRes::Proved);
```

## Core Concepts

### Terms

Terms represent objects in logic:

```rust
use vampire_prover::{Function, Term};

// Constants (0-ary functions)
let socrates = Function::constant("socrates");

// Variables
let x = Term::new_var(0);

// Function applications
let succ = Function::new("succ", 1);
let one = succ.with(Function::constant("0"));
```

### Sorts (Types)

Vampire supports multi-sorted logic (TFF). You can use built-in sorts or define your own:

```rust
use vampire_prover::Sort;

let int_sort = Sort::int();       // Built-in Integer sort
let real_sort = Sort::real();     // Built-in Real sort
let list_sort = Sort::new("list"); // Custom user-defined sort
```

### Formulas

Formulas are logical statements:

```rust
use vampire_prover::{Predicate, forall, exists};

let p = Predicate::new("P", 1);
let q = Predicate::new("Q", 1);

// Connectives
let both = p.with(x) & q.with(x);   // Conjunction
let either = p.with(x) | q.with(x); // Disjunction
let implies = p.with(x) >> q.with(x); // Implication
let equiv = p.with(x).iff(q.with(x)); // Biconditional

// Quantifiers
let all = forall(|x| p.with(x));    // ∀x. P(x)
let some = exists(|x| p.with(x));   // ∃x. P(x)
```

## Typed Logic (TFF)

You can define symbols with specific argument and return sorts:

```rust
use vampire_prover::{Sort, Predicate, Function, forall_typed};

let person = Sort::new("person");
let father_of = Function::typed("father_of", &[person], person);
let is_happy = Predicate::typed("is_happy", &[person]);

// Typed quantification: ∀(x: person). is_happy(father_of(x))
let formula = forall_typed(person, |x| is_happy.with(father_of.with(x)));
```

## Interpreted Arithmetic

Vampire provides built-in support for interpreted arithmetic symbols:

```rust
use vampire_prover::{Sort, Function, Predicate, Interp, Term, Problem, Options, ProofRes};

let int = Sort::int();
let plus = Function::interpreted("$sum", Interp::IntPlus);
let less = Predicate::interpreted("$less", Interp::IntLess);

// x + 1 < 5
let x = Term::new_var(0);
let formula = less.with([plus.with([x, Term::int("1")]), Term::int("5")]);

// You can also use ergonomic conversion from Rust literals
let formula = less.with([plus.with([x, 1]), 5]);
```

## Clausification

You can use Vampire to transform any complex formula into Conjunctive Normal Form (CNF):

```rust
use vampire_prover::{Predicate, Problem, Options, forall};

let p = Predicate::new("P", 1);
let q = Predicate::new("Q", 1);

// Axiom: ∀x. P(x) ↔ Q(x)
let mut problem = Problem::new(Options::new())
    .with_axiom(forall(|x| p.with(x).iff(q.with(x))));

// Extract clauses
problem.clausify();
let clauses = problem.get_cnf();

// clauses will contain strings like:
// [ "¬'P'(X0) | 'Q'(X0)", "'P'(X0) | ¬'Q'(X0)" ]
```

## Operators

The crate provides convenient operators for logical connectives:

| Operator | Logic | Example |
|----------|-------|---------|
| `&` | Conjunction (AND) | `p & q` |
| `\|` | Disjunction (OR) | `p \| q` |
| `>>` | Implication | `p >> q` |
| `!` | Negation (NOT) | `!p` |
| `.iff()` | Biconditional (IFF) | `p.iff(q)` |
| `.eq()` | Equality | `x.eq(y)` |
| `.typed_eq(s)` | Typed Equality | `x.typed_eq(y, sort)` |

## Proof Results

When you call `Problem::solve()`, you get one of three results:

- `ProofRes::Proved` - The conjecture was successfully proved
- `ProofRes::Unprovable` - The axioms are insufficient to prove the conjecture
- `ProofRes::Unknown(reason)` - Vampire could not determine the result (e.g., `Timeout`)

## Limitations and Stability

### Process-Global Static State
The underlying Vampire C++ library was originally designed as a command-line tool where each execution starts with a fresh process. When used as a library, Vampire maintains extensive **process-global static state**, including:
- **Term Sharing Caches**: Hash-consed terms and literals.
- **Global Signature**: The registry of all function and predicate symbols.
- **Saturation Engine State**: Statistics, ordering diagrams, and timer configurations.

#### Critical Stability Rules:
1. **Handle Persistence**: Rust handles like `Predicate`, `Function`, and `Sort` store IDs that refer to the global signature. If you call `vampire_sys::vampire_reset()`, these handles become invalid and using them will cause a **SIGSEGV**.
2. **Sequential Testing**: Running multiple complex proofs in the same process can occasionally lead to internal memory corruption in Vampire's saturation engine. It is highly recommended to run tests with `--test-threads=1`.
3. **Thread Safety**: This crate uses a global mutex to serialize all calls to Vampire. While safe to call from multiple threads, only one proof can execute at any given time.

## Thread Safety
**Important**: As noted above, the underlying Vampire library is not thread-safe. This crate protects all operations with a global mutex.

## License

This Rust crate is licensed under either of the Apache License, Version 2.0 or the MIT license. The underlying Vampire theorem prover library is licensed under the **BSD 3-Clause License**.
