//! Low-level FFI bindings to the Vampire theorem prover.
//!
//! This crate provides unsafe, raw bindings to the Vampire C API. It is intended
//! as an implementation detail of the `vampire` crate and is not meant to be used
//! directly.
//!
//! # Usage
//!
//! **You probably want the [`vampire`](https://docs.rs/vampire) crate instead.**
//!
//! The `vampire` crate provides a safe, ergonomic Rust API on top of these raw
//! bindings. This crate (`vampire-sys`) only provides the low-level unsafe
//! functions and types needed to interface with the Vampire C++ library.
//!
//! # Building
//!
//! This crate automatically builds the Vampire library from source using CMake
//! during compilation. You need:
//! - CMake 3.10 or later
//! - A C++ compiler (GCC, Clang, or MSVC)
//! - Standard C++ library
//!
//! # Thread Safety
//!
//! The underlying Vampire library is **not thread-safe**. The `vampire` crate
//! handles this by protecting all calls with a global mutex. If you use this
//! crate directly, you must implement your own synchronization.
//!
//! # Platform Support
//!
//! This crate supports:
//! - Linux (links against libstdc++)
//! - macOS (links against libc++)
//! - Other platforms may work but are untested

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

mod bindings;
pub use bindings::*;
