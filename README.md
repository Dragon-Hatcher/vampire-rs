# vampire-rs

Rust bindings to the [Vampire](https://vprover.github.io/) theorem prover for first-order logic with equality.

## Overview

This workspace provides safe, ergonomic Rust bindings to Vampire, a state-of-the-art automated theorem prover. Vampire is adept at proving first order theorem in arbitrary mathematical domains.

## Crates

### [`vampire`](vampire/)

The main crate providing safe, high-level Rust bindings. **This is what you want to use.**

```toml
[dependencies]
vampire = "0.1.0"
```

**Features:**
- Safe Rust API with builder pattern
- Ergonomic operators for logical connectives (`&`, `|`, `>>`, `!`)
- Automatic variable management for quantifiers
- Thread-safe (operations protected by mutex)
- Comprehensive documentation and examples

**Quick Example:**

```rust
use vampire::{Function, Predicate, Problem, ProofRes, forall};

let is_mortal = Predicate::new("mortal", 1);
let is_man = Predicate::new("man", 1);
let men_are_mortal = forall(|x| is_man.with(&[x]) >> is_mortal.with(&[x]));

let socrates = Function::constant("socrates");

let result = Problem::new()
    .with_axiom(is_man.with(&[socrates]))
    .with_axiom(men_are_mortal)
    .conjecture(is_mortal.with(&[socrates]))
    .solve();

assert_eq!(result, ProofRes::Proved);
```

See the [vampire README](vampire/README.md) for detailed documentation.

### [`vampire-sys`](vampire-sys/)

Low-level FFI bindings to the Vampire C API. This is an implementation detail used by the `vampire` crate. You should not use this directly unless you need unsafe access to the raw C API.

## Building

### Requirements

- **Rust** 1.70 or later (uses edition 2024)
- **CMake** 3.10 or later
- **C++ compiler** (GCC, Clang, or MSVC)
- Standard C++ library

### Build Process

The Vampire C++ library is automatically built from source during compilation via CMake. Simply run:

```bash
cargo build
```


## Platform Support

Tested on:
- **Linux** (Ubuntu, Debian, Arch, etc.)
- **macOS** (x86_64 and ARM64)

## Project Structure

```
vampire-rs/
├── vampire/          # Safe high-level Rust bindings
│   ├── src/
│   ├── examples/     # Example programs
│   └── README.md
├── vampire-sys/      # Low-level FFI bindings (internal)
│   ├── src/
│   └── README.md
├── vampire-lib/      # Vampire C++ library (submodule or vendored)
└── README.md         # This file
```

## License

### Rust Bindings

The Rust bindings (`vampire` and `vampire-sys` crates) are licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Vampire Theorem Prover

The underlying Vampire theorem prover library is licensed under the **BSD 3-Clause License**.

```
Vampire is copyright (C) 2020 by its authors and contributors and their
institutional affiliations. All rights reserved.
```

See [vampire-lib/LICENCE](vampire-lib/LICENCE) for the complete Vampire license text.

When distributing applications that use this crate, you must comply with the Vampire BSD 3-Clause license requirements, which include:
- Retaining the Vampire copyright notice
- Reproducing the Vampire license in your documentation/distribution
- Not using the names of Vampire contributors to endorse your product without permission

## Resources

- [Vampire Prover Website](https://vprover.github.io/)
- [First-Order Logic on Wikipedia](https://en.wikipedia.org/wiki/First-order_logic)
- [Automated Theorem Proving](https://en.wikipedia.org/wiki/Automated_theorem_proving)

## Acknowledgments

This project provides Rust bindings to the Vampire theorem prover, developed by the Vampire team. All credit for the theorem proving capabilities goes to the original Vampire developers.
