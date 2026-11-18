//! Prover options — pure data, no FFI.
//!
//! Consumed by the FFI solve path (when `integrated-prover` is on) and
//! carried through lowering. Fields are `pub(crate)` so `ffi.rs` can read
//! them while applying to the C++ library.

use std::time::Duration;

/// Configuration for the theorem prover.
///
/// Used at lowering + solve time. Options are pure data and can be
/// constructed without any C++ linkage.
///
/// # Examples
///
/// ```
/// use std::time::Duration;
/// use vampire_prover::Options;
///
/// // Defaults: no timeout, no extra options.
/// let _ = Options::new();
///
/// // Common configuration: 5-second timeout, CASC portfolio mode.
/// let mut opts = Options::new();
/// opts.timeout(Duration::from_secs(5));
/// opts.set_option("mode", "casc");
/// ```
#[derive(Debug, Clone, Default)]
pub struct Options {
    pub(crate) timeout: Option<Duration>,
    pub(crate) extra_options: Vec<(String, String)>,
}

impl Options {
    /// Creates fresh options: no timeout and no extra key/value settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets a proof-search timeout. If the prover exceeds this limit it
    /// returns `ProofRes::Unknown(UnknownReason::Timeout)`.
    pub fn timeout(&mut self, duration: Duration) -> &mut Self {
        self.timeout = Some(duration);
        self
    }

    /// Sets an arbitrary Vampire option by name and value.
    ///
    /// This maps directly to Vampire's `--name value` command-line flag.
    /// For example, `set_option("mode", "casc")` enables CASC portfolio
    /// mode.
    pub fn set_option(
        &mut self,
        name: impl Into<String>,
        value: impl Into<String>,
    ) -> &mut Self {
        self.extra_options.push((name.into(), value.into()));
        self
    }

    /// Returns the configured proof-search timeout, if any.
    pub fn timeout_duration(&self) -> Option<Duration> {
        self.timeout
    }

    /// Returns the registered extra key/value options.
    pub fn extras(&self) -> &[(String, String)] {
        &self.extra_options
    }
}
