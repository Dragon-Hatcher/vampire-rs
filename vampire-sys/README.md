# vampire-sys

Low-level FFI bindings to the [Vampire](https://vprover.github.io/) theorem prover.

## ⚠️  You probably want the `vampire` crate instead

This crate provides unsafe, raw C bindings to the Vampire library. It is intended as an implementation detail and is not meant to be used directly.

**For safe, ergonomic Rust bindings, use the [`vampire-prover`](https://crates.io/crates/vampire-prover) crate.**

## What This Crate Provides

- Raw C function bindings generated from the Vampire C API
- Unsafe types and structures matching the C interface
- Automatic building of the Vampire C++ library via CMake

## Building

This crate automatically compiles the Vampire library from source using CMake. You need:

- **CMake** 3.10 or later
- **C++ compiler** (GCC, Clang, or MSVC)
- Standard C++ library

The build process:
1. Uses CMake to configure the Vampire C++ library
2. Builds the `vampire_lib` static library target
3. Links against the appropriate C++ standard library for your platform

## Platform Support

Tested and supported platforms:
- **Linux** - Links against `libstdc++`
- **macOS** - Links against `libc++`
- **Windows** - Should work with MSVC (untested)

## Thread Safety

**The Vampire library is NOT thread-safe.** If you use this crate directly, you must implement your own synchronization (e.g., with a global mutex). The `vampire` crate handles this for you.

## License

### Rust Bindings

This FFI crate is licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](../LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](../LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Vampire Theorem Prover

The underlying Vampire theorem prover library that this crate links to is licensed under the **BSD 3-Clause License**. See [vampire-lib/LICENCE](../vampire-lib/LICENCE) for the complete license text.

When distributing applications using this crate, you must comply with both the Rust bindings license and the Vampire BSD 3-Clause license requirements.

## Links

- [Vampire Prover](https://vprover.github.io/)
- [vampire crate](https://crates.io/crates/vampire-prover) - Safe Rust bindings
