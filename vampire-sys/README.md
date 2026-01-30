# vampire-sys

Low-level FFI bindings to the [Vampire](https://vprover.github.io/) theorem prover.

## ⚠️  You probably want the `vampire` crate instead

This crate provides unsafe, raw C bindings to the Vampire library. It is intended as an implementation detail and is not meant to be used directly.

**For safe, ergonomic Rust bindings, use the [`vampire`](https://crates.io/crates/vampire) crate.**

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

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](../LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](../LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Links

- [Vampire Prover](https://vprover.github.io/)
- [vampire crate](https://crates.io/crates/vampire) - Safe Rust bindings
