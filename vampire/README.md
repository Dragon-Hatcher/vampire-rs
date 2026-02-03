# vampire

Safe Rust bindings to the [Vampire](https://vprover.github.io/) theorem prover for first-order logic with equality.

## Overview

This crate provides a high-level, safe Rust interface to Vampire, a state-of-the-art automated theorem prover. Vampire can prove theorems, check satisfiability, and find counterexamples in various mathematical domains including:

- Propositional and first-order logic
- Equality reasoning
- Group theory and algebra
- Graph properties
- Program verification
- Mathematical proofs

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

Terms represent objects in first-order logic:

```rust
use vampire_prover::{Function, Term};

// Constants (0-ary functions)
let zero = Function::constant("0");
let socrates = Function::constant("socrates");

// Variables
let x = Term::new_var(0);
let y = Term::new_var(1);

// Function applications
let succ = Function::new("succ", 1);
let one = succ.with(zero);

let add = Function::new("add", 2);
let sum = add.with([x, y]);
```

**Note**: Function and predicate symbols are interned. Calling `Function::new` or `Predicate::new` with the same name and arity multiple times will return the same symbol. It's safe to use the same name with different arities - they will be treated as distinct symbols.

### Formulas

Formulas are logical statements:

```rust
use vampire_prover::{Function, Predicate, forall, exists};

let p = Predicate::new("P", 1);
let q = Predicate::new("Q", 1);
let x = Function::constant("x");

// Atomic formulas
let px = p.with(x);
let qx = q.with(x);

// Logical connectives
let both = px & qx;          // P(x) ∧ Q(x) - conjunction
let either = px | qx;        // P(x) ∨ Q(x) - disjunction
let implies = px >> qx;      // P(x) → Q(x) - implication
let not_px = !px;            // ¬P(x) - negation
let equiv = px.iff(qx);      // P(x) ↔ Q(x) - biconditional

// Quantifiers
let all = forall(|x| p.with(x));        // ∀x. P(x)
let some = exists(|x| p.with(x));       // ∃x. P(x)
```

### Equality

Equality is a built-in predicate:

```rust
use vampire_prover::{Function, forall};

let f = Function::new("f", 1);
let x = Function::constant("x");

// Direct equality
let eq1 = x.eq(x);  // x = x

// Equality in quantified formulas
let reflexive = forall(|x| x.eq(x));  // ∀x. x = x
```

## Examples

### Graph Reachability

Prove that a path exists in a graph using transitivity:

```rust
use vampire_prover::{Function, Predicate, Problem, ProofRes, Options, forall};

let edge = Predicate::new("edge", 2);
let path = Predicate::new("path", 2);

// Create nodes
let a = Function::constant("a");
let b = Function::constant("b");
let c = Function::constant("c");
let d = Function::constant("d");

// Axiom: Edges are paths
let edges_are_paths = forall(|x| forall(|y|
    edge.with([x, y]) >> path.with([x, y])
));

// Axiom: Paths are transitive
let transitivity = forall(|x| forall(|y| forall(|z|
    (path.with([x, y]) & path.with([y, z])) >> path.with([x, z])
)));

// Prove there's a path from a to d
let result = Problem::new(Options::new())
    .with_axiom(edges_are_paths)
    .with_axiom(transitivity)
    .with_axiom(edge.with([a, b]))
    .with_axiom(edge.with([b, c]))
    .with_axiom(edge.with([c, d]))
    .conjecture(path.with([a, d]))
    .solve();

assert_eq!(result, ProofRes::Proved);
```

### Group Theory

Prove the left identity from the standard group axioms:

```rust
use vampire_prover::{Function, Problem, ProofRes, Options, Term, forall};

let mult = Function::new("mult", 2);
let inv = Function::new("inv", 1);
let one = Function::constant("1");

let mul = |x: Term, y: Term| mult.with([x, y]);

// Group axioms
let right_identity = forall(|x| mul(x, one).eq(x));
let right_inverse = forall(|x| mul(x, inv.with(x)).eq(one));
let associativity = forall(|x| forall(|y| forall(|z|
    mul(mul(x, y), z).eq(mul(x, mul(y, z)))
)));

// Prove left identity
let left_identity = forall(|x| mul(one, x).eq(x));

let result = Problem::new(Options::new())
    .with_axiom(right_identity)
    .with_axiom(right_inverse)
    .with_axiom(associativity)
    .conjecture(left_identity)
    .solve();

assert_eq!(result, ProofRes::Proved);
```

### Set Theory

Prove properties about sets:

```rust
use vampire_prover::{Function, Predicate, Problem, Options, forall};

let member = Predicate::new("member", 2);
let subset = Predicate::new("subset", 2);

// Define subset: A ⊆ B ↔ ∀x. x ∈ A → x ∈ B
let subset_def = forall(|a| forall(|b|
    subset.with([a, b]).iff(
        forall(|x| member.with([x, a]) >> member.with([x, b]))
    )
));

// Prove subset is reflexive: ∀A. A ⊆ A
let reflexive = forall(|a| subset.with([a, a]));

let result = Problem::new(Options::new())
    .with_axiom(subset_def)
    .conjecture(reflexive)
    .solve();

assert_eq!(result, ProofRes::Proved);
```

## Configuration Options

You can configure the prover's behavior using the `Options` struct:

```rust
use vampire_prover::{Problem, Options};
use std::time::Duration;

// Default options (no timeout)
let problem = Problem::new(Options::new());

// Set a timeout
let problem = Problem::new(Options::new().timeout(Duration::from_secs(5)));
```

Currently supported options:
- **Timeout**: Set a time limit for the prover. If exceeded, the result will be `ProofRes::Unknown(UnknownReason::Timeout)`.

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

## Proof Results

When you call `Problem::solve()`, you get one of three results:

- `ProofRes::Proved` - The conjecture was successfully proved from the axioms
- `ProofRes::Unprovable` - The axioms are insufficient to prove the conjecture (note: the conjecture could still be true or false, but the given axioms cannot establish it)
- `ProofRes::Unknown(reason)` - Vampire could not determine if the axioms imply the conjecture:
  - `UnknownReason::Timeout` - Time limit exceeded
  - `UnknownReason::MemoryLimit` - Memory limit exceeded
  - `UnknownReason::Incomplete` - Problem uses incomplete logic
  - `UnknownReason::Unknown` - Unknown reason

## Thread Safety

**Important**: The underlying Vampire library is not thread-safe. This crate protects all operations with a global mutex, so while you can safely use the library from multiple threads, all proof operations will be serialized. Only one proof can execute at a time.

## License

### Rust Bindings

This Rust crate is licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Vampire Theorem Prover

The underlying Vampire theorem prover library is licensed under the **BSD 3-Clause License**. See the [Vampire LICENCE file](https://github.com/vprover/vampire/blob/master/LICENCE) for details.

When distributing applications using this crate, you must comply with both the Rust bindings license (your choice of MIT or Apache-2.0) and the Vampire BSD 3-Clause license requirements.
