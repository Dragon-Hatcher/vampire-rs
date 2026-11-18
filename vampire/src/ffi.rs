use crate::lock::synced;
use crate::options::Options;
use std::{
    collections::HashMap,
    ffi::CString,
    fmt::Display,
    ops::{BitAnd, BitOr, Index, Not, Shr},
};
use vampire_sys::{self as sys, vampire_unit_t, vampire_interpretation_t};


/// Interpreted theory symbols for arithmetic and more.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Interp {
    Equal,
    IntGreater,
    IntGreaterEqual,
    IntLess,
    IntLessEqual,
    IntDivides,
    IntSuccessor,
    IntUnaryMinus,
    IntPlus,
    IntMinus,
    IntMultiply,
    IntQuotientE,
    IntRemainderT,
    IntAbs,
    RatGreater,
    RatGreaterEqual,
    RatLess,
    RatLessEqual,
    RatPlus,
    RatMinus,
    RatMultiply,
    RatQuotient,
    RealGreater,
    RealGreaterEqual,
    RealLess,
    RealLessEqual,
    RealPlus,
    RealMinus,
    RealMultiply,
    RealQuotient,
    // Rounding (argument sort → integer)
    IntFloor,
    IntCeiling,
    IntTruncate,
    IntRound,
    RatFloor,
    RatCeiling,
    RatTruncate,
    RatRound,
    RealFloor,
    RealCeiling,
    RealTruncate,
    RealRound,
    // Type coercions
    IntToInt,
    IntToRat,
    IntToReal,
    RatToInt,
    RatToRat,
    RatToReal,
    RealToInt,
    RealToRat,
    RealToReal,
}

impl Interp {
    fn to_raw(self) -> vampire_interpretation_t {
        match self {
            Interp::Equal => sys::vampire_interpretation_t_VAMPIRE_INTERP_EQUAL,
            Interp::IntGreater => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_GREATER,
            Interp::IntGreaterEqual => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_GREATER_EQUAL,
            Interp::IntLess => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_LESS,
            Interp::IntLessEqual => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_LESS_EQUAL,
            Interp::IntDivides => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_DIVIDES,
            Interp::IntSuccessor => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_SUCCESSOR,
            Interp::IntUnaryMinus => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_UNARY_MINUS,
            Interp::IntPlus => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_PLUS,
            Interp::IntMinus => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_MINUS,
            Interp::IntMultiply => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_MULTIPLY,
            Interp::IntQuotientE => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_QUOTIENT_E,
            Interp::IntRemainderT => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_REMAINDER_T,
            Interp::IntAbs => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_ABS,
            Interp::RatGreater => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_GREATER,
            Interp::RatGreaterEqual => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_GREATER_EQUAL,
            Interp::RatLess => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_LESS,
            Interp::RatLessEqual => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_LESS_EQUAL,
            Interp::RatPlus => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_PLUS,
            Interp::RatMinus => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_MINUS,
            Interp::RatMultiply => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_MULTIPLY,
            Interp::RatQuotient => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_QUOTIENT,
            Interp::RealGreater => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_GREATER,
            Interp::RealGreaterEqual => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_GREATER_EQUAL,
            Interp::RealLess => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_LESS,
            Interp::RealLessEqual => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_LESS_EQUAL,
            Interp::RealPlus => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_PLUS,
            Interp::RealMinus => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_MINUS,
            Interp::RealMultiply => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_MULTIPLY,
            Interp::RealQuotient => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_QUOTIENT,
            Interp::IntFloor    => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_FLOOR,
            Interp::IntCeiling  => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_CEILING,
            Interp::IntTruncate => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_TRUNCATE,
            Interp::IntRound    => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_ROUND,
            Interp::RatFloor    => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_FLOOR,
            Interp::RatCeiling  => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_CEILING,
            Interp::RatTruncate => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_TRUNCATE,
            Interp::RatRound    => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_ROUND,
            Interp::RealFloor   => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_FLOOR,
            Interp::RealCeiling => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_CEILING,
            Interp::RealTruncate=> sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_TRUNCATE,
            Interp::RealRound   => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_ROUND,
            Interp::IntToInt    => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_TO_INT,
            Interp::IntToRat    => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_TO_RAT,
            Interp::IntToReal   => sys::vampire_interpretation_t_VAMPIRE_INTERP_INT_TO_REAL,
            Interp::RatToInt    => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_TO_INT,
            Interp::RatToRat    => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_TO_RAT,
            Interp::RatToReal   => sys::vampire_interpretation_t_VAMPIRE_INTERP_RAT_TO_REAL,
            Interp::RealToInt   => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_TO_INT,
            Interp::RealToRat   => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_TO_RAT,
            Interp::RealToReal  => sys::vampire_interpretation_t_VAMPIRE_INTERP_REAL_TO_REAL,
        }
    }
}

/// Trait for types that can be converted into a [`Term`].
///
/// This enables ergonomic use of Rust literals (like `1`, `2`) in term construction.
pub trait IntoTerm {
    /// Convert this type into a Vampire [`Term`].
    fn into_term(self) -> Term;
}

impl IntoTerm for Term {
    fn into_term(self) -> Term {
        self
    }
}

impl IntoTerm for i32 {
    fn into_term(self) -> Term {
        Term::int(&self.to_string())
    }
}

impl IntoTerm for i64 {
    fn into_term(self) -> Term {
        Term::int(&self.to_string())
    }
}

impl IntoTerm for u32 {
    fn into_term(self) -> Term {
        Term::int(&self.to_string())
    }
}

impl IntoTerm for u64 {
    fn into_term(self) -> Term {
        Term::int(&self.to_string())
    }
}

impl IntoTerm for f32 {
    fn into_term(self) -> Term {
        Term::real(&self.to_string())
    }
}

impl IntoTerm for f64 {
    fn into_term(self) -> Term {
        Term::real(&self.to_string())
    }
}

/// Trait for types that can be converted into term arguments.
///
/// This trait allows `.with()` methods on [`Function`] and [`Predicate`] to accept
/// different argument formats for convenience:
/// - Single term or literal: `f.with(x)`, `f.with(1)`
/// - Homogeneous array: `f.with([x, y])`, `f.with([1, 2])`
/// - Heterogeneous tuple: `f.with((x, 1))`
pub trait IntoTermArgs {
    /// Calls the given function with a slice of terms representing the arguments.
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R;
}

impl IntoTermArgs for () {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        f(&[])
    }
}

impl<'a> IntoTermArgs for &'a [Term] {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        f(self)
    }
}

impl IntoTermArgs for Term {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        f(std::slice::from_ref(&self))
    }
}

impl IntoTermArgs for i32 {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let t = self.into_term();
        f(std::slice::from_ref(&t))
    }
}

impl IntoTermArgs for i64 {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let t = self.into_term();
        f(std::slice::from_ref(&t))
    }
}

impl IntoTermArgs for u32 {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let t = self.into_term();
        f(std::slice::from_ref(&t))
    }
}

impl IntoTermArgs for u64 {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let t = self.into_term();
        f(std::slice::from_ref(&t))
    }
}

impl IntoTermArgs for f32 {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let t = self.into_term();
        f(std::slice::from_ref(&t))
    }
}

impl IntoTermArgs for f64 {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let t = self.into_term();
        f(std::slice::from_ref(&t))
    }
}

impl<'a, const N: usize> IntoTermArgs for &'a [Term; N] {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        f(self)
    }
}

impl<'a> IntoTermArgs for &'a Vec<Term> {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        f(self)
    }
}

impl<T: IntoTerm, const N: usize> IntoTermArgs for [T; N] {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms = self.map(|t| t.into_term());
        f(&terms)
    }
}

impl<T: IntoTerm> IntoTermArgs for Vec<T> {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms: Vec<Term> = self.into_iter().map(|t| t.into_term()).collect();
        f(&terms)
    }
}

impl<T1: IntoTerm, T2: IntoTerm> IntoTermArgs for (T1, T2) {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms = [self.0.into_term(), self.1.into_term()];
        f(&terms)
    }
}

impl<T1: IntoTerm, T2: IntoTerm, T3: IntoTerm> IntoTermArgs for (T1, T2, T3) {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms = [self.0.into_term(), self.1.into_term(), self.2.into_term()];
        f(&terms)
    }
}

impl<T1: IntoTerm, T2: IntoTerm, T3: IntoTerm, T4: IntoTerm> IntoTermArgs for (T1, T2, T3, T4) {
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms = [
            self.0.into_term(),
            self.1.into_term(),
            self.2.into_term(),
            self.3.into_term(),
        ];
        f(&terms)
    }
}

impl<T1: IntoTerm, T2: IntoTerm, T3: IntoTerm, T4: IntoTerm, T5: IntoTerm> IntoTermArgs
    for (T1, T2, T3, T4, T5)
{
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms = [
            self.0.into_term(),
            self.1.into_term(),
            self.2.into_term(),
            self.3.into_term(),
            self.4.into_term(),
        ];
        f(&terms)
    }
}

impl<T1: IntoTerm, T2: IntoTerm, T3: IntoTerm, T4: IntoTerm, T5: IntoTerm, T6: IntoTerm, T7: IntoTerm>
    IntoTermArgs for (T1, T2, T3, T4, T5, T6, T7)
{
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms = [
            self.0.into_term(),
            self.1.into_term(),
            self.2.into_term(),
            self.3.into_term(),
            self.4.into_term(),
            self.5.into_term(),
            self.6.into_term(),
        ];
        f(&terms)
    }
}

impl<
        T1: IntoTerm,
        T2: IntoTerm,
        T3: IntoTerm,
        T4: IntoTerm,
        T5: IntoTerm,
        T6: IntoTerm,
        T7: IntoTerm,
        T8: IntoTerm,
    > IntoTermArgs for (T1, T2, T3, T4, T5, T6, T7, T8)
{
    fn with_slice<R>(self, f: impl FnOnce(&[Term]) -> R) -> R {
        let terms = [
            self.0.into_term(),
            self.1.into_term(),
            self.2.into_term(),
            self.3.into_term(),
            self.4.into_term(),
            self.5.into_term(),
            self.6.into_term(),
            self.7.into_term(),
        ];
        f(&terms)
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
/// use vampire_prover::ffi::Function;
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
#[derive(Debug, Clone)]
pub struct Function {
    id: u32,
    arity: u32,
    name: String,
    arg_sorts: Vec<Sort>,
    ret_sort: Option<Sort>,
    is_typed: bool,
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl Eq for Function {}
impl std::hash::Hash for Function {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.id.hash(state); }
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
    /// use vampire_prover::ffi::Function;
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
            let name_cstr = CString::new(name).expect("valid c string");
            let function = unsafe { sys::vampire_add_function(name_cstr.as_ptr(), arity) };
            Self {
                id: function,
                arity,
                name: name.to_string(),
                arg_sorts: Vec::new(),
                ret_sort: None,
                is_typed: false,
            }
        })
    }

    /// Returns the arity (number of arguments) of this function.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Function;
    ///
    /// let f = Function::new("f", 3);
    /// assert_eq!(f.arity(), 3);
    /// ```
    pub fn arity(&self) -> u32 {
        self.arity
    }

    /// Creates a constant term (0-ary function).
    ///
    /// This is a convenience method equivalent to `Function::new(name, 0).with(())`.
    /// Constants represent specific objects in the domain.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the constant
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Function;
    ///
    /// let socrates = Function::constant("socrates");
    /// let zero = Function::constant("0");
    /// ```
    pub fn constant(name: &str) -> Term {
        Self::new(name, 0).with(())
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
    /// use vampire_prover::ffi::{Function, Term};
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
        args.with_slice(|slice| {
            if slice.is_empty() {
                synced(|_| Term {
                    id: unsafe { sys::vampire_constant(self.id) },
                })
            } else {
                Term::new_function(self, slice)
            }
        })
    }

    /// Creates a new typed function symbol with explicit sort annotations.
    ///
    /// The sort of each argument and the return sort are specified. Like [`Function::new`],
    /// this is idempotent when called with the same name and sorts; only the first call
    /// registers the type. Do not mix with [`Function::new`] for the same name, as that
    /// would register conflicting types.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Sort, Function};
    ///
    /// let person = Sort::new("person");
    /// let father_of = Function::typed("father_of", &[person.clone()], person);
    /// ```
    pub fn typed(name: &str, arg_sorts: &[Sort], return_sort: Sort) -> Self {
        synced(|_| {
            let name_cstr = CString::new(name).expect("valid c string");
            let mut indices: Vec<u32> = arg_sorts.iter().map(|s| s.id).collect();
            let id = unsafe {
                sys::vampire_add_typed_function(
                    name_cstr.as_ptr(),
                    indices.as_mut_ptr(),
                    indices.len(),
                    return_sort.id,
                )
            };
            Self {
                id,
                arity: arg_sorts.len() as u32,
                name: name.to_string(),
                arg_sorts: arg_sorts.to_vec(),
                ret_sort: Some(return_sort),
                is_typed: true,
            }
        })
    }

    /// Creates a new interpreted function symbol.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Function, Interp};
    ///
    /// let plus = Function::interpreted("$sum", Interp::IntPlus);
    /// ```
    pub fn interpreted(name: &str, interp: Interp) -> Self {
        synced(|_| {
            let name_cstr = CString::new(name).expect("valid c string");
            let id = unsafe { sys::vampire_add_interpreted_function(name_cstr.as_ptr(), interp.to_raw()) };
            let arity = match interp {
                Interp::IntUnaryMinus | Interp::IntSuccessor | Interp::IntAbs
                | Interp::IntFloor    | Interp::IntCeiling   | Interp::IntTruncate  | Interp::IntRound
                | Interp::RatFloor    | Interp::RatCeiling   | Interp::RatTruncate  | Interp::RatRound
                | Interp::RealFloor   | Interp::RealCeiling  | Interp::RealTruncate | Interp::RealRound
                | Interp::IntToInt    | Interp::IntToRat     | Interp::IntToReal
                | Interp::RatToInt    | Interp::RatToRat     | Interp::RatToReal
                | Interp::RealToInt   | Interp::RealToRat    | Interp::RealToReal => 1,
                _ => 2,
            };
            Self {
                id,
                arity,
                name: name.to_string(),
                arg_sorts: Vec::new(),
                ret_sort: None,
                is_typed: false,
            }
        })
    }

    /// Returns the TPTP type declaration line for this function, or `None` for
    /// untyped and interpreted functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Sort, Function};
    ///
    /// let list = Sort::new("list");
    /// let nil = Function::typed("nil", &[], list.clone());
    /// assert!(nil.tptp_decl().is_some());
    ///
    /// let untyped = Function::new("f", 1);
    /// assert_eq!(untyped.tptp_decl(), None);
    /// ```
    pub fn tptp_decl(&self) -> Option<String> {
        if !self.is_typed {
            return None;
        }
        let ret = self.ret_sort.as_ref().unwrap().tptp_name();
        if self.arg_sorts.is_empty() {
            Some(format!("tff(fn_{}, type, {}: {}).", self.name, self.name, ret))
        } else {
            let args = self.arg_sorts.iter()
                .map(|s| s.tptp_name())
                .collect::<Vec<_>>()
                .join(" * ");
            Some(format!("tff(fn_{}_{}, type, {}: ({}) > {}).", self.name, self.arity, self.name, args, ret))
        }
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
/// use vampire_prover::ffi::{Function, Predicate};
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
#[derive(Debug, Clone)]
pub struct Predicate {
    id: u32,
    arity: u32,
    name: String,
    arg_sorts: Vec<Sort>,
    is_typed: bool,
}

impl PartialEq for Predicate {
    fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl Eq for Predicate {}
impl std::hash::Hash for Predicate {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.id.hash(state); }
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
    /// use vampire_prover::ffi::Predicate;
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
        synced(|_| {
            let name_cstr = CString::new(name).expect("valid c string");
            let predicate = unsafe { sys::vampire_add_predicate(name_cstr.as_ptr(), arity) };
            Self {
                id: predicate,
                arity,
                name: name.to_string(),
                arg_sorts: Vec::new(),
                is_typed: false,
            }
        })
    }

    /// Returns the arity (number of arguments) of this predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Predicate;
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
    /// use vampire_prover::ffi::{Function, Predicate};
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
        args.with_slice(|slice| Formula::new_predicate(self, slice))
    }

    /// Creates a new typed predicate symbol with explicit sort annotations.
    ///
    /// The sort of each argument is specified. Like [`Predicate::new`], this is
    /// idempotent when called with the same name and sorts; only the first call
    /// registers the type. Do not mix with [`Predicate::new`] for the same name,
    /// as that would register conflicting types.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Sort, Predicate};
    ///
    /// let person = Sort::new("person");
    /// let animal = Sort::new("animal");
    /// let owns = Predicate::typed("owns", &[person, animal]);
    /// ```
    pub fn typed(name: &str, arg_sorts: &[Sort]) -> Self {
        synced(|_| {
            let name_cstr = CString::new(name).expect("valid c string");
            let mut indices: Vec<u32> = arg_sorts.iter().map(|s| s.id).collect();
            let id = unsafe {
                sys::vampire_add_typed_predicate(
                    name_cstr.as_ptr(),
                    indices.as_mut_ptr(),
                    indices.len(),
                )
            };
            Self {
                id,
                arity: arg_sorts.len() as u32,
                name: name.to_string(),
                arg_sorts: arg_sorts.to_vec(),
                is_typed: true,
            }
        })
    }

    /// Creates a new interpreted predicate symbol.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Predicate, Interp};
    ///
    /// let less = Predicate::interpreted("$less", Interp::IntLess);
    /// ```
    pub fn interpreted(name: &str, interp: Interp) -> Self {
        synced(|_| {
            let name_cstr = CString::new(name).expect("valid c string");
            let id = unsafe { sys::vampire_add_interpreted_predicate(name_cstr.as_ptr(), interp.to_raw()) };
            Self {
                id,
                arity: 2,
                name: name.to_string(),
                arg_sorts: Vec::new(),
                is_typed: false,
            }
        })
    }

    /// Returns the TPTP type declaration line for this predicate, or `None` for
    /// untyped and interpreted predicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Sort, Predicate};
    ///
    /// let person = Sort::new("person");
    /// let mortal = Predicate::typed("mortal", &[person]);
    /// assert!(mortal.tptp_decl().is_some());
    ///
    /// let untyped = Predicate::new("p", 1);
    /// assert_eq!(untyped.tptp_decl(), None);
    /// ```
    pub fn tptp_decl(&self) -> Option<String> {
        if !self.is_typed {
            return None;
        }
        let args = self.arg_sorts.iter()
            .map(|s| s.tptp_name())
            .collect::<Vec<_>>()
            .join(" * ");
        if self.arg_sorts.len() == 1 {
            Some(format!("tff(pred_{}_{}, type, {}: {} > $o).", self.name, self.arity, self.name, args))
        } else {
            Some(format!("tff(pred_{}_{}, type, {}: ({}) > $o).", self.name, self.arity, self.name, args))
        }
    }
}

/// A sort (type) in typed first-order logic (TFF).
///
/// Sorts are used to partition the domain into distinct types. Functions and
/// predicates can be declared with specific sort signatures, and quantified
/// variables can be annotated with their sort.
///
/// # Examples
///
/// ```
/// use vampire_prover::ffi::{Sort, Function, Predicate, forall_typed};
///
/// // User-defined sort
/// let person = Sort::new("person");
///
/// // Built-in sorts
/// let i = Sort::default_sort(); // $i (untyped individual)
/// let z = Sort::int();          // $int
/// ```
#[derive(Debug, Clone)]
pub struct Sort {
    id: u32, // typeCon index in Vampire's signature
    name: String,
    is_builtin: bool,
}

impl PartialEq for Sort {
    fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl Eq for Sort {}
impl std::hash::Hash for Sort {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.id.hash(state); }
}

impl Sort {
    /// Creates (or retrieves) a user-defined sort with the given name.
    ///
    /// Idempotent: calling with the same name always returns the same sort.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Sort;
    ///
    /// let person = Sort::new("person");
    /// let person2 = Sort::new("person");
    /// assert_eq!(person, person2);
    /// ```
    pub fn new(name: &str) -> Self {
        synced(|_| {
            let name_cstr = CString::new(name).expect("valid c string");
            let id = unsafe { sys::vampire_add_sort(name_cstr.as_ptr()) };
            Self { id, name: name.to_string(), is_builtin: false }
        })
    }

    /// Returns the Boolean sort (`$o`) — HOL/THF.
    pub fn bool_sort() -> Self {
        synced(|_| Self {
            id: unsafe { sys::vampire_sort_bool() },
            name: "$o".to_string(),
            is_builtin: true,
        })
    }

    /// Registers the arrow sort `from > to` (HOL/THF).  The result is usable
    /// everywhere a sort is (typed symbols, typed quantifiers).
    pub fn arrow(from: &Sort, to: &Sort) -> Self {
        synced(|_| Self {
            id: unsafe { sys::vampire_sort_arrow(from.id, to.id) },
            name: format!("({} > {})", from.name, to.name),
            is_builtin: true,
        })
    }

    /// Returns the default individual sort (`$i`).
    pub fn default_sort() -> Self {
        synced(|_| Self {
            id: unsafe { sys::vampire_sort_default() },
            name: "$i".to_string(),
            is_builtin: true,
        })
    }

    /// Returns the integer sort (`$int`).
    pub fn int() -> Self {
        synced(|_| Self {
            id: unsafe { sys::vampire_sort_int() },
            name: "$int".to_string(),
            is_builtin: true,
        })
    }

    /// Returns the real number sort (`$real`).
    pub fn real() -> Self {
        synced(|_| Self {
            id: unsafe { sys::vampire_sort_real() },
            name: "$real".to_string(),
            is_builtin: true,
        })
    }

    /// Returns the rational number sort (`$rat`).
    pub fn rational() -> Self {
        synced(|_| Self {
            id: unsafe { sys::vampire_sort_rational() },
            name: "$rat".to_string(),
            is_builtin: true,
        })
    }

    /// Returns the TPTP name for this sort (e.g. `"$int"`, `"$real"`, or a user-defined name).
    pub fn tptp_name(&self) -> &str {
        &self.name
    }

    /// Returns the TPTP type declaration line for this sort, or `None` for built-in sorts.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Sort;
    ///
    /// let person = Sort::new("person");
    /// assert_eq!(person.tptp_decl(), Some("tff(sort_person, type, person: $tType).".to_string()));
    ///
    /// let int_sort = Sort::int();
    /// assert_eq!(int_sort.tptp_decl(), None);
    /// ```
    pub fn tptp_decl(&self) -> Option<String> {
        if self.is_builtin {
            None
        } else {
            Some(format!("tff(sort_{}, type, {}: $tType).", self.name, self.name))
        }
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
/// use vampire_prover::ffi::{Function, Term};
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
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Term {
    id: *mut sys::vampire_term_t,
}

impl Term {
    /// HOL application `self @ arg` (curried).  `self` must be a proper term
    /// (constant or application) — its arrow sort determines the result.
    pub fn hol_app(&self, arg: &Term) -> Term {
        synced(|_| Term {
            id: unsafe { sys::vampire_hol_app(self.id, arg.id) },
        })
    }

    /// HOL application with an explicit head sort — required when `self` is
    /// a VARIABLE (`P @ X` under a `! [P: $i > $o]` binder), whose sort
    /// cannot be inferred from the term itself.
    pub fn hol_app_sorted(&self, head_sort: &Sort, arg: &Term) -> Term {
        synced(|_| Term {
            id: unsafe { sys::vampire_hol_app_sorted(self.id, head_sort.id, arg.id) },
        })
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        synced(|_| unsafe { sys::vampire_term_equal(self.id, other.id) })
    }
}

impl Eq for Term {}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        synced(|_| unsafe { sys::vampire_term_hash(self.id) }).hash(state);
    }
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Term({})", self.to_string())
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
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
    /// use vampire_prover::ffi::Function;
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
    /// use vampire_prover::ffi::{Function, Term};
    ///
    /// let add = Function::new("add", 2);
    /// let x = Term::new_var(0);
    /// let y = Term::new_var(1);
    ///
    /// let sum = Term::new_function(&add, &[x, y]);
    /// ```
    pub fn new_function(func: &Function, args: &[Term]) -> Self {
        assert!(args.len() == func.arity() as usize);

        synced(|_| unsafe {
            let arg_count = args.len();
            let args = std::mem::transmute(args.as_ptr());
            let term = sys::vampire_term(func.id, args, arg_count);
            Self { id: term }
        })
    }

    /// Converts this term to a TPTP string representation.
    pub fn to_tptp(&self) -> String {
        self.to_string()
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
    /// use vampire_prover::ffi::Term;
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
    /// use vampire_prover::ffi::Term;
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
    /// use vampire_prover::ffi::{Function, forall};
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

    /// Creates a typed equality formula between this term and another, with an explicit sort.
    ///
    /// Use this instead of [`Term::eq`] when working with TFF problems where the sort
    /// of the equality must be stated explicitly.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Sort, Function, forall_typed};
    ///
    /// let person = Sort::new("person");
    /// let alice = Function::typed("alice", &[], person.clone()).with(());
    /// let bob = Function::typed("bob", &[], person.clone()).with(());
    ///
    /// let are_equal = alice.typed_eq(bob, person);
    /// ```
    pub fn typed_eq(self, rhs: Term, sort: Sort) -> Formula {
        Formula::new_eq_typed(self, rhs, sort)
    }

    /// Creates an interpreted integer constant term.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Term;
    ///
    /// let hundred = Term::int("100");
    /// ```
    pub fn int(value: &str) -> Self {
        synced(|_| {
            let value_cstr = CString::new(value).expect("valid c string");
            let id = unsafe { sys::vampire_add_integer_constant(value_cstr.as_ptr()) };
            Self { id: unsafe { sys::vampire_constant(id) } }
        })
    }

    /// Creates an interpreted rational constant term.
    pub fn rational(value: &str) -> Self {
        synced(|_| {
            let value_cstr = CString::new(value).expect("valid c string");
            let id = unsafe { sys::vampire_add_rational_constant(value_cstr.as_ptr()) };
            Self { id: unsafe { sys::vampire_constant(id) } }
        })
    }

    /// Creates an interpreted real constant term.
    pub fn real(value: &str) -> Self {
        synced(|_| {
            let value_cstr = CString::new(value).expect("valid c string");
            let id = unsafe { sys::vampire_add_real_constant(value_cstr.as_ptr()) };
            Self { id: unsafe { sys::vampire_constant(id) } }
        })
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
/// use vampire_prover::ffi::{Function, Predicate, forall};
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
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Formula {
    pub(crate) id: *mut sys::vampire_formula_t,
}

impl Formula {
    /// A Boolean-sorted term in formula position (`X: $o` as a formula) —
    /// HOL/THF.
    pub fn from_bool_term(t: &Term) -> Formula {
        synced(|_| Formula {
            id: unsafe { sys::vampire_bool_term_formula(t.id) },
        })
    }

    /// This formula as a Boolean-sorted term (FOOL: a compound formula in a
    /// `$o` argument position) — HOL/THF.
    pub fn as_bool_term(&self) -> Term {
        synced(|_| Term {
            id: unsafe { sys::vampire_formula_term(self.id) },
        })
    }

    /// Returns the raw FFI pointer to the underlying Vampire formula.
    ///
    /// This is an advanced API intended for use by crates that need to pass
    /// formulas directly to vampire-sys FFI calls (e.g. the clausify path in
    /// sigmakee-rs-core). The caller must ensure the pointer is only used
    /// while the `Formula` is live.
    pub fn as_ptr(&self) -> *mut sys::vampire_formula_t {
        self.id
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        synced(|_| unsafe { sys::vampire_formula_equal(self.id, other.id) })
    }
}

impl Eq for Formula {}

impl std::hash::Hash for Formula {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        synced(|_| unsafe { sys::vampire_formula_hash(self.id) }).hash(state);
    }
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Formula({})", self.to_string())
    }
}

impl std::fmt::Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
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
    /// use vampire_prover::ffi::{Function, Predicate};
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
    /// use vampire_prover::ffi::{Function, Predicate, Formula};
    ///
    /// let mortal = Predicate::new("mortal", 1);
    /// let socrates = Function::constant("socrates");
    ///
    /// let formula = Formula::new_predicate(&mortal, &[socrates]);
    /// ```
    pub fn new_predicate(pred: &Predicate, args: &[Term]) -> Self {
        assert!(args.len() == pred.arity() as usize);

        synced(|_| unsafe {
            let arg_count = args.len();
            let args = std::mem::transmute(args.as_ptr());
            let lit = sys::vampire_lit(pred.id, true, args, arg_count);
            let atom = sys::vampire_atom(lit);
            Self { id: atom }
        })
    }

    /// Converts this formula to a TPTP string representation.
    pub fn to_tptp(&self) -> String {
        self.to_string()
    }

    /// Creates an equality formula between two terms.
    ///
    /// This is typically called via [`Term::eq`] rather than directly.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::{Function, Formula};
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
    /// use vampire_prover::ffi::{Function, Predicate, Formula};
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
    /// use vampire_prover::ffi::{Function, Predicate, Formula};
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
    /// use vampire_prover::ffi::{Function, Predicate, Formula};
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

    /// Creates the true (tautology) formula.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Formula;
    ///
    /// let t = Formula::new_true();
    /// ```
    pub fn new_true() -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_true() };
            Self { id }
        })
    }

    /// Creates the false (contradiction) formula.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ffi::Formula;
    ///
    /// let f = Formula::new_false();
    /// ```
    pub fn new_false() -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_false() };
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
    /// use vampire_prover::ffi::{Function, Predicate, Formula, Term};
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
    /// use vampire_prover::ffi::{Function, Predicate, Formula, Term};
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
    /// use vampire_prover::ffi::{Function, Predicate};
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
    /// use vampire_prover::ffi::{Function, Predicate, forall};
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

    /// Creates a universally quantified formula with a sort annotation on the bound variable.
    ///
    /// The [`forall_typed`] helper function provides a more ergonomic interface.
    ///
    /// # Arguments
    ///
    /// * `var` - The index of the variable to quantify
    /// * `sort` - The sort of the bound variable
    /// * `f` - The formula body
    pub fn new_forall_typed(var: u32, sort: Sort, f: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_forall_typed(var, sort.id, f.id) };
            Self { id }
        })
    }

    /// Creates an existentially quantified formula with a sort annotation on the bound variable.
    ///
    /// The [`exists_typed`] helper function provides a more ergonomic interface.
    ///
    /// # Arguments
    ///
    /// * `var` - The index of the variable to quantify
    /// * `sort` - The sort of the bound variable
    /// * `f` - The formula body
    pub fn new_exists_typed(var: u32, sort: Sort, f: Formula) -> Self {
        synced(|_| {
            let id = unsafe { sys::vampire_exists_typed(var, sort.id, f.id) };
            Self { id }
        })
    }

    /// Creates a typed equality formula between two terms with an explicit sort.
    ///
    /// Use [`Term::typed_eq`] for a more ergonomic interface.
    ///
    /// # Arguments
    ///
    /// * `lhs` - Left-hand side term
    /// * `rhs` - Right-hand side term
    /// * `sort` - The sort of both terms
    pub fn new_eq_typed(lhs: Term, rhs: Term, sort: Sort) -> Self {
        synced(|_| unsafe {
            let lit = sys::vampire_typed_eq(true, lhs.id, rhs.id, sort.id);
            let atom = sys::vampire_atom(lit);
            Self { id: atom }
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
/// use vampire_prover::ffi::{Function, Predicate, forall};
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
/// use vampire_prover::ffi::{Function, Predicate, forall};
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
/// use vampire_prover::ffi::{Function, Predicate, exists};
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
/// use vampire_prover::ffi::{Function, Predicate, exists, forall};
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

/// Creates a universally quantified formula over a typed variable using a closure.
///
/// This is the typed analogue of [`forall`]. The closure receives a fresh variable
/// term; the variable is bound with the given sort annotation.
///
/// # Arguments
///
/// * `sort` - The sort of the quantified variable
/// * `f` - A closure that takes a [`Term`] and returns a [`Formula`]
///
/// # Examples
///
/// ```
/// use vampire_prover::ffi::{Sort, Predicate, Function, forall_typed};
///
/// let person = Sort::new("person");
/// let mortal = Predicate::typed("mortal", &[person.clone()]);
///
/// // ∀x: person. mortal(x)
/// let all_mortal = forall_typed(person, |x| mortal.with(x));
/// ```
pub fn forall_typed<F: FnOnce(Term) -> Formula>(sort: Sort, f: F) -> Formula {
    let (var, var_idx) = Term::free_var();
    let formula = f(var);
    Formula::new_forall_typed(var_idx, sort, formula)
}

/// Creates an existentially quantified formula over a typed variable using a closure.
///
/// This is the typed analogue of [`exists`]. The closure receives a fresh variable
/// term; the variable is bound with the given sort annotation.
///
/// # Arguments
///
/// * `sort` - The sort of the quantified variable
/// * `f` - A closure that takes a [`Term`] and returns a [`Formula`]
///
/// # Examples
///
/// ```
/// use vampire_prover::ffi::{Sort, Predicate, Function, exists_typed};
///
/// let person = Sort::new("person");
/// let happy = Predicate::typed("happy", &[person.clone()]);
///
/// // ∃x: person. happy(x)
/// let someone_happy = exists_typed(person, |x| happy.with(x));
/// ```
pub fn exists_typed<F: FnOnce(Term) -> Formula>(sort: Sort, f: F) -> Formula {
    let (var, var_idx) = Term::free_var();
    let formula = f(var);
    Formula::new_exists_typed(var_idx, sort, formula)
}

/// Implements the `&` operator for conjunction (AND).
///
/// # Examples
///
/// ```
/// use vampire_prover::ffi::{Function, Predicate};
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
/// use vampire_prover::ffi::{Function, Predicate};
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
/// use vampire_prover::ffi::{Function, Predicate};
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
/// use vampire_prover::ffi::{Function, Predicate};
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

// `Options` is now defined in `crate::ir::options` so it can be constructed
// without the C++ backend. Imported at the top of this file.

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
/// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem, ProofRes, forall};
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
/// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem};
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
/// Whether a problem uses untyped first-order logic (FOF) or typed (TFF).
///
/// Set at construction time via [`Problem::new`] (FOF) or [`Problem::new_tff`] (TFF).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicMode {
    /// First-order logic without sort annotations (FOF).
    Fof,
    /// Typed first-order logic with sort annotations (TFF).
    Tff,
}

#[derive(Debug, Clone)]
pub struct Problem {
    options: Options,
    mode: LogicMode,
    axioms: Vec<Formula>,
    /// Caller-supplied name of each axiom (parallel to `axioms`), set by
    /// [`Problem::with_named_axiom`].
    axiom_names: Vec<Option<String>>,
    /// Vampire's unit number for each axiom (parallel to `axioms`), recorded
    /// by the most recent solve so proof steps can be traced back to inputs.
    axiom_units: Vec<u32>,
    conjecture: Option<Formula>,
    sort_decls: Vec<Sort>,
    fn_decls: Vec<Function>,
    pred_decls: Vec<Predicate>,
}

impl Problem {
    /// Creates a new problem from a TPTP string.
    ///
    /// Replaces the options on this problem.
    pub fn with_options(mut self, options: Options) -> Self {
        self.options = options;
        self
    }

    /// Creates a new, empty problem with the given options.

    ///
    /// # Arguments
    ///
    /// * `options` - Configuration options for the prover
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Options;
/// use vampire_prover::ffi::{Problem};
    /// use std::time::Duration;
    ///
    /// // Default options
    /// let problem = Problem::new(Options::new());
    /// ```
    /// Creates a new FOF (untyped first-order logic) problem.
    pub fn new(options: Options) -> Self {
        Self {
            options,
            mode: LogicMode::Fof,
            axioms: Vec::new(),
            axiom_names: Vec::new(),
            axiom_units: Vec::new(),
            conjecture: None,
            sort_decls: Vec::new(),
            fn_decls: Vec::new(),
            pred_decls: Vec::new(),
        }
    }

    /// Creates a new TFF (typed first-order logic) problem.
    ///
    /// Use this when working with typed sorts, functions, and predicates.
    /// Call [`declare_sort`][Self::declare_sort], [`declare_function`][Self::declare_function],
    /// and [`declare_predicate`][Self::declare_predicate] to register type declarations
    /// that will be emitted by [`to_tptp`][Self::to_tptp].
    pub fn new_tff(options: Options) -> Self {
        Self {
            options,
            mode: LogicMode::Tff,
            axioms: Vec::new(),
            axiom_names: Vec::new(),
            axiom_units: Vec::new(),
            conjecture: None,
            sort_decls: Vec::new(),
            fn_decls: Vec::new(),
            pred_decls: Vec::new(),
        }
    }

    /// Returns the logic mode of this problem.
    pub fn mode(&self) -> LogicMode {
        self.mode
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
    /// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem, forall};
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
        self.axiom_names.push(None);
        self
    }

    /// Adds an axiom carrying a caller-chosen `name`.
    ///
    /// The name is not passed to Vampire; it is attached to the proof steps
    /// that use this axiom as an input, available through
    /// [`ProofStep::axiom_name`] after [`Problem::solve_and_prove`]. Use it to
    /// map proof steps back to the caller's own identifiers (e.g. the source
    /// sentence an axiom was translated from).
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Options;
    /// use vampire_prover::ffi::{Function, Predicate, Problem, ProofRes};
    ///
    /// let p = Predicate::new("P", 1);
    /// let x = Function::constant("x");
    ///
    /// let (result, proof) = Problem::new(Options::new())
    ///     .with_named_axiom(p.with(x), "p_of_x")
    ///     .conjecture(p.with(x))
    ///     .solve_and_prove();
    ///
    /// assert_eq!(result, ProofRes::Proved);
    /// let proof = proof.unwrap();
    /// let names: Vec<&str> = proof
    ///     .steps()
    ///     .iter()
    ///     .filter_map(|s| s.axiom_name())
    ///     .collect();
    /// assert_eq!(names, ["p_of_x"]);
    /// ```
    pub fn with_named_axiom(&mut self, f: Formula, name: impl Into<String>) -> &mut Self {
        self.axioms.push(f);
        self.axiom_names.push(Some(name.into()));
        self
    }

    /// Borrow the axiom vector for structured-clausify paths.
    pub fn axioms_raw(&self) -> &[Formula] {
        &self.axioms
    }

    /// Borrow the conjecture for structured-clausify paths.
    pub fn conjecture_raw(&self) -> Option<&Formula> {
        self.conjecture.as_ref()
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
    /// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem, forall};
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

    /// Registers a sort declaration for TPTP output (TFF problems only).
    ///
    /// Only user-defined sorts produce declarations; built-in sorts (`$int`, etc.) are
    /// ignored. Duplicate declarations (by sort id) are silently skipped.
    /// In FOF mode this is a no-op.
    pub fn declare_sort(&mut self, s: Sort) -> &mut Self {
        if self.mode == LogicMode::Tff {
            if s.tptp_decl().is_some() && !self.sort_decls.iter().any(|x| x.id == s.id) {
                self.sort_decls.push(s);
            }
        }
        self
    }

    /// Registers a function declaration for TPTP output (TFF problems only).
    ///
    /// Only typed functions produce declarations. Duplicates and FOF-mode calls are ignored.
    pub fn declare_function(&mut self, f: Function) -> &mut Self {
        if self.mode == LogicMode::Tff {
            if f.is_typed && !self.fn_decls.iter().any(|x| x.id == f.id) {
                self.fn_decls.push(f);
            }
        }
        self
    }

    /// Registers a predicate declaration for TPTP output (TFF problems only).
    ///
    /// Only typed predicates produce declarations. Duplicates and FOF-mode calls are ignored.
    pub fn declare_predicate(&mut self, p: Predicate) -> &mut Self {
        if self.mode == LogicMode::Tff {
            if p.is_typed && !self.pred_decls.iter().any(|x| x.id == p.id) {
                self.pred_decls.push(p);
            }
        }
        self
    }

    /// Serialises this problem as a TPTP string.
    ///
    /// Uses `tff(...)` syntax for problems created with [`Problem::new_tff`],
    /// and `fof(...)` for problems created with [`Problem::new`].
    /// Type declarations registered via [`declare_sort`][Self::declare_sort] /
    /// [`declare_function`][Self::declare_function] /
    /// [`declare_predicate`][Self::declare_predicate] are emitted first.
    pub fn to_tptp(&self) -> String {
        let kw = match self.mode {
            LogicMode::Tff => "tff",
            LogicMode::Fof => "fof",
        };

        let mut out = String::new();

        for s in &self.sort_decls {
            if let Some(decl) = s.tptp_decl() {
                out.push_str(&decl);
                out.push('\n');
            }
        }

        for f in &self.fn_decls {
            if let Some(decl) = f.tptp_decl() {
                out.push_str(&decl);
                out.push('\n');
            }
        }

        for p in &self.pred_decls {
            if let Some(decl) = p.tptp_decl() {
                out.push_str(&decl);
                out.push('\n');
            }
        }

        for (i, ax) in self.axioms.iter().enumerate() {
            out.push_str(&format!("{}(axiom_{}, axiom, {}).\n", kw, i, ax.to_tptp()));
        }

        if let Some(conj) = &self.conjecture {
            out.push_str(&format!("{}(conjecture, conjecture, {}).\n", kw, conj.to_tptp()));
        }

        out
    }

    unsafe fn unsynce_solve(&mut self) -> ProofRes {
        unsafe {
            sys::vampire_prepare_for_next_proof();

            // Apply timeout option if set
            if let Some(timeout) = self.options.timeout {
                let ms = timeout.as_millis().max(1);
                sys::vampire_set_time_limit_milliseconds(ms as i32);
            }

            // Apply extra options (e.g. mode=casc)
            for (name, value) in &self.options.extra_options {
                let name_c = CString::new(name.as_str()).expect("valid c string");
                let value_c = CString::new(value.as_str()).expect("valid c string");
                sys::vampire_set_option(name_c.as_ptr(), value_c.as_ptr());
            }

            let mut units = Vec::new();

            self.axiom_units.clear();
            for axiom in &self.axioms {
                let axiom_unit = sys::vampire_axiom_formula(axiom.id);
                self.axiom_units.push(sys::vampire_unit_number(axiom_unit));
                units.push(axiom_unit);
            }
            if let Some(conjecture) = self.conjecture {
                let conjecture_unit = sys::vampire_conjecture_formula(conjecture.id);
                units.push(conjecture_unit);
            }

            let problem = sys::vampire_problem_from_units(units.as_mut_ptr(), units.len());
            let proof_res = sys::vampire_prove(problem);

            ProofRes::new_from_raw(proof_res)
        }
    }

    /// Solves the problem in an isolated child process.
    ///
    /// This uses the `fork()` system call to create a duplicate of the current process.
    /// The solver runs in the child process, ensuring that any global state corruption
    /// or memory leaks in the underlying Vampire C++ library are wiped clean when
    /// the child exits. The parent process remains unaffected.
    ///
    /// This is highly recommended for persistent applications making repeated solver calls.
    pub fn solve_isolated(&mut self) -> ProofRes {
        use std::io::{Read, Write};
        use std::os::unix::io::FromRawFd;

        synced(|_| {
            let mut fds = [0i32; 2];
            if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
                return ProofRes::Unknown(UnknownReason::Other("Failed to create pipe".to_string()));
            }

            let pid = unsafe { libc::fork() };
            if pid < 0 {
                unsafe {
                    libc::close(fds[0]);
                    libc::close(fds[1]);
                }
                return ProofRes::Unknown(UnknownReason::Other("Fork failed".to_string()));
            }

            if pid == 0 {
                // child: run the solve and write the outcome back through the pipe
                unsafe { libc::close(fds[0]) };
                let result = unsafe { self.unsynce_solve() };
                
                let (code, msg) = match result {
                    ProofRes::Proved => (0u8, "".to_string()),
                    ProofRes::Unprovable => (1u8, "".to_string()),
                    ProofRes::Unknown(reason) => {
                        let (c, m) = match reason {
                            UnknownReason::Timeout => (2, "".to_string()),
                            UnknownReason::MemoryLimit => (3, "".to_string()),
                            UnknownReason::Incomplete => (4, "".to_string()),
                            UnknownReason::Unknown => (5, "".to_string()),
                            UnknownReason::Other(s) => (6, s),
                        };
                        (c, m)
                    }
                };

                let mut writer = unsafe { std::fs::File::from_raw_fd(fds[1]) };
                let _ = writer.write_all(&[code]);
                if !msg.is_empty() {
                    let _ = writer.write_all(msg.as_bytes());
                }
                
                // Use _exit to prevent running Rust destructors in the child
                unsafe { libc::_exit(0) };
            } else {
                // parent: wait for the child and read the outcome back
                unsafe { libc::close(fds[1]) };
                let mut reader = unsafe { std::fs::File::from_raw_fd(fds[0]) };

                let mut status = 0i32;
                unsafe { libc::waitpid(pid, &mut status, 0) };

                if libc::WIFSIGNALED(status) {
                    let sig = libc::WTERMSIG(status);
                    return ProofRes::Unknown(UnknownReason::Other(format!("Solver process crashed with signal {}", sig)));
                }

                let mut buf = [0u8; 1];
                if reader.read_exact(&mut buf).is_err() {
                    return ProofRes::Unknown(UnknownReason::Other("Failed to read result from solver process".to_string()));
                }

                match buf[0] {
                    0 => ProofRes::Proved,
                    1 => ProofRes::Unprovable,
                    2 => ProofRes::Unknown(UnknownReason::Timeout),
                    3 => ProofRes::Unknown(UnknownReason::MemoryLimit),
                    4 => ProofRes::Unknown(UnknownReason::Incomplete),
                    5 => ProofRes::Unknown(UnknownReason::Unknown),
                    6 => {
                        let mut reason = String::new();
                        let _ = reader.read_to_string(&mut reason);
                        ProofRes::Unknown(UnknownReason::Other(reason))
                    }
                    _ => ProofRes::Unknown(UnknownReason::Other("Invalid result code from solver process".to_string())),
                }
            }
        })
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
    /// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem, ProofRes, forall};
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
        synced(|_| unsafe { self.unsynce_solve() })
    }

    /// Converts the problem formulas into Conjunctive Normal Form (CNF) clauses.
    ///
    /// This method invokes Vampire's preprocessing engine to clausify all axioms
    /// and the conjecture.
    ///
    /// # Returns
    ///
    /// A vector of strings, where each string represents one CNF clause.
    ///
    /// # Known limitation
    ///
    /// This path hands formulas directly to Vampire's `NewCNF` without the
    /// full `Shell::Preprocess` pipeline that `vampire_prove` runs.  `NewCNF`
    /// asserts `g->connective() != IMP` in its binary-formula branch, so
    /// any axiom or conjecture containing an un-eliminated `Imp`
    /// connective will crash the process.  The structured variant
    /// [`crate::clausify::clausify`] (`ir::Problem::clausify`) performs a
    /// Rust-side `Imp` elimination pre-pass before dispatching, and is
    /// the recommended entry point for callers that need clausification.
    pub fn clausify(&mut self) -> Vec<String> {
        synced(|_| unsafe {
            sys::vampire_prepare_for_next_proof();

            // Apply timeout option if set
            if let Some(timeout) = self.options.timeout {
                let ms = timeout.as_millis().max(1);
                sys::vampire_set_time_limit_milliseconds(ms as i32);
            }

            let mut unit_ptrs = Vec::new();
            for axiom in &self.axioms {
                unit_ptrs.push(sys::vampire_axiom_formula(axiom.id));
            }
            if let Some(conjecture) = self.conjecture {
                unit_ptrs.push(sys::vampire_conjecture_formula(conjecture.id));
            }

            let problem = sys::vampire_problem_from_units(unit_ptrs.as_mut_ptr(), unit_ptrs.len());

            // The clauses must exist before vampire_get_cnf can extract them.
            sys::vampire_clausify(problem);
            
            let mut clauses_ptr: *mut *mut ::std::os::raw::c_char = std::ptr::null_mut();
            let mut count: usize = 0;
            
            let res = sys::vampire_get_cnf(problem, &mut clauses_ptr, &mut count);
            
            let mut result = Vec::with_capacity(count);
            if res == 0 && !clauses_ptr.is_null() {
                for i in 0..count {
                    let ptr = *clauses_ptr.add(i);
                    if !ptr.is_null() {
                        let c_str = std::ffi::CStr::from_ptr(ptr);
                        result.push(c_str.to_string_lossy().into_owned());
                    }
                }
                sys::vampire_free_string_array(clauses_ptr, count);
            }
            
            for u in unit_ptrs {
                sys::vampire_free_unit(u);
            }
            
            result
        })
    }

    /// Solves the problem and, if proved, returns the proof.
    ///
    /// This is like [`Problem::solve`] but also extracts a [`Proof`] when the
    /// conjecture is successfully proved. If the result is anything other than
    /// [`ProofRes::Proved`], the second element of the tuple is `None`.
    ///
    /// # Returns
    ///
    /// A tuple of `(ProofRes, Option<Proof>)`. The `Option<Proof>` is `Some` only
    /// when the result is [`ProofRes::Proved`].
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem, ProofRes, forall};
    ///
    /// let p = Predicate::new("P", 1);
    /// let x = Function::constant("x");
    ///
    /// let (result, proof) = Problem::new(Options::new())
    ///     .with_axiom(p.with(x))
    ///     .conjecture(p.with(x))
    ///     .solve_and_prove();
    ///
    /// assert_eq!(result, ProofRes::Proved);
    /// assert!(proof.is_some());
    /// println!("{}", proof.unwrap());
    /// ```
    pub fn solve_and_prove(&mut self) -> (ProofRes, Option<Proof>) {
        synced(|_| unsafe {
            let res = self.unsynce_solve();

            let ProofRes::Proved = res else {
                return (res, None);
            };

            let refutation = sys::vampire_get_refutation();
            let mut proof = Proof::from_refutation(refutation);
            proof.attribute_axioms(&self.axiom_units, &self.axiom_names);

            (res, Some(proof))
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
/// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem, ProofRes, forall};
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
/// use vampire_prover::ffi::{ProofRes, UnknownReason};
///
/// let result = ProofRes::Unknown(UnknownReason::Timeout);
///
/// if let ProofRes::Unknown(reason) = result {
///     match reason {
///         UnknownReason::Timeout => println!("Ran out of time"),
///         UnknownReason::MemoryLimit => println!("Ran out of memory"),
///         UnknownReason::Incomplete => println!("Problem uses incomplete logic"),
///         UnknownReason::Unknown => println!("Unknown reason"),
///         UnknownReason::Other(msg) => println!("Error: {}", msg),
///     }
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    /// An internal error occurred in the solver or the process isolation layer.
    Other(String),
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

/// A proof produced by the Vampire theorem prover.
///
/// A `Proof` is a sequence of [`ProofStep`]s that together form a complete
/// derivation of a contradiction from the negated conjecture and axioms.
/// Each step records the inference rule used and the indices of the premises
/// (earlier steps) it was derived from.
///
/// Proofs are obtained via [`Problem::solve_and_prove`].
///
/// # Display
///
/// `Proof` implements [`std::fmt::Display`], which prints each step on its own
/// line in the format `<index>: <conclusion> [<rule> <premise-indices>]`.
///
/// # Examples
///
/// ```
/// use vampire_prover::Options;
/// use vampire_prover::ffi::{Function, Predicate, Problem, ProofRes};
///
/// let p = Predicate::new("P", 1);
/// let x = Function::constant("x");
///
/// let (_, proof) = Problem::new(Options::new())
///     .with_axiom(p.with(x))
///     .conjecture(p.with(x))
///     .solve_and_prove();
///
/// if let Some(proof) = proof {
///     for step in proof.steps() {
///         println!("{}: {:?}", step.discovery_order(), step.rule());
///     }
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    steps: Vec<ProofStep>,
}

impl Proof {
    unsafe fn from_refutation(refutation: *mut vampire_unit_t) -> Self {
        unsafe {
            let mut steps_ptr = std::ptr::null_mut();
            let mut steps_len: usize = 0;
            let success = sys::vampire_extract_proof(refutation, &mut steps_ptr, &mut steps_len);
            assert!(success == 0);

            let vsteps = std::slice::from_raw_parts(steps_ptr, steps_len);
            let mut vsteps = vsteps.to_vec();
            vsteps.sort_by_key(|s| s.id);

            let mut steps = Vec::new();
            let mut step_map = HashMap::new();

            for vstep in vsteps {
                let discovery_order = vstep.id;
                let rule = ProofRule::from_raw(vstep.rule, vstep.input_type);
                let premises = if vstep.premise_count == 0 {
                    Vec::new()
                } else {
                    std::slice::from_raw_parts(vstep.premise_ids, vstep.premise_count)
                        .iter()
                        .map(|p| step_map[p])
                        .collect()
                };

                let conclusion = sys::vampire_unit_as_formula(vstep.unit);
                let conclusion = Formula { id: conclusion };

                step_map.insert(discovery_order, steps.len());
                let step = ProofStep {
                    discovery_order,
                    rule,
                    premises,
                    conclusion,
                    axiom_index: None,
                    axiom_name: None,
                };
                steps.push(step);
            }

            sys::vampire_free_proof_steps(steps_ptr, steps_len);

            Self { steps }
        }
    }

    /// Mark every input-axiom step with the index (and name, if any) of the
    /// problem axiom it is. `units[i]` is the unit number Vampire gave axiom
    /// `i`; an input step's [`ProofStep::discovery_order`] is its unit number.
    fn attribute_axioms(&mut self, units: &[u32], names: &[Option<String>]) {
        let index_of: HashMap<u32, usize> =
            units.iter().enumerate().map(|(i, &u)| (u, i)).collect();
        for step in &mut self.steps {
            if step.rule != ProofRule::Axiom {
                continue;
            }
            if let Some(&i) = index_of.get(&step.discovery_order) {
                step.axiom_index = Some(i);
                step.axiom_name = names.get(i).cloned().flatten();
            }
        }
    }

    /// Returns all proof steps in the order Vampire discovered them.
    ///
    /// Steps are sorted by their [`ProofStep::discovery_order`]. Because each
    /// step's premises always have a lower discovery order than the step itself,
    /// this ordering is also a valid topological ordering of the proof DAG.
    pub fn steps(&self) -> &[ProofStep] {
        &self.steps
    }

    /// Iterates over proof steps in topological order (discovery order).
    ///
    /// This is equivalent to iterating over [`Proof::steps`] and is provided
    /// for clarity when the topological property matters.
    pub fn topo_iter(&self) -> impl Iterator<Item = &ProofStep> {
        self.steps.iter()
    }
}

impl Display for Proof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, step) in self.steps().iter().enumerate() {
            writeln!(
                f,
                "{}: {} [{:?}{}]",
                i,
                step.conclusion(),
                step.rule(),
                step.premises()
                    .iter()
                    .fold(String::new(), |s, p| s + " " + &p.to_string())
            )?
        }

        Ok(())
    }
}

impl Index<usize> for Proof {
    type Output = ProofStep;

    fn index(&self, index: usize) -> &Self::Output {
        &self.steps[index]
    }
}

/// The inference rule used to derive a [`ProofStep`].
///
/// Each step in a [`Proof`] was produced by one of these rules. Input steps
/// (axioms and the negated conjecture) use [`ProofRule::Axiom`] or
/// [`ProofRule::NegatedConjecture`]. All other variants represent internal
/// Vampire inference rules applied during the proof search.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProofRule {
    // claude: don't document what these individual rules are.
    Axiom,
    NegatedConjecture,
    Rectify,
    Flatten,
    EENFTransformation,
    CNFTransformation,
    NNFTransformation,
    SkolemSymbolIntroduction,
    Skolemize,
    Superposition,
    ForwardDemodulation,
    BackwardDemodulation,
    ForwardSubsumptionResolution,
    Resolution,
    TrivialInequalityRemoval,
    Avatar,
    Other,
}

impl ProofRule {
    fn from_raw(rule: u32, input_type: u32) -> Self {
        if rule == sys::vampire_inference_rule_t_INPUT {
            if input_type == sys::vampire_input_type_t_VAMPIRE_AXIOM {
                Self::Axiom
            } else if input_type == sys::vampire_input_type_t_VAMPIRE_NEGATED_CONJECTURE {
                Self::NegatedConjecture
            } else if input_type == sys::vampire_input_type_t_VAMPIRE_CONJECTURE {
                // Original conjecture before negation -- treat as NegatedConjecture
                // since Vampire proves by refutation.
                Self::NegatedConjecture
            } else {
                // Unknown input type (e.g. hypothesis) -- treat as axiom.
                Self::Axiom
            }
        } else if rule == sys::vampire_inference_rule_t_RECTIFY {
            Self::Rectify
        } else if rule == sys::vampire_inference_rule_t_FLATTEN {
            Self::Flatten
        } else if rule == sys::vampire_inference_rule_t_ENNF {
            Self::EENFTransformation
        } else if rule == sys::vampire_inference_rule_t_CLAUSIFY {
            Self::CNFTransformation
        } else if rule == sys::vampire_inference_rule_t_NNF {
            Self::NNFTransformation
        } else if rule == sys::vampire_inference_rule_t_SKOLEM_SYMBOL_INTRODUCTION {
            Self::Skolemize
        } else if rule == sys::vampire_inference_rule_t_SKOLEMIZE {
            Self::SkolemSymbolIntroduction
        } else if rule == sys::vampire_inference_rule_t_SUPERPOSITION {
            Self::Superposition
        } else if rule == sys::vampire_inference_rule_t_FORWARD_DEMODULATION {
            Self::ForwardDemodulation
        } else if rule == sys::vampire_inference_rule_t_BACKWARD_DEMODULATION {
            Self::BackwardDemodulation
        } else if rule == sys::vampire_inference_rule_t_FORWARD_SUBSUMPTION_RESOLUTION {
            Self::ForwardSubsumptionResolution
        } else if rule == sys::vampire_inference_rule_t_RESOLUTION {
            Self::Resolution
        } else if rule == sys::vampire_inference_rule_t_TRIVIAL_INEQUALITY_REMOVAL {
            Self::TrivialInequalityRemoval
        } else if rule == sys::vampire_inference_rule_t_AVATAR_DEFINITION
            || rule == sys::vampire_inference_rule_t_AVATAR_COMPONENT
            || rule == sys::vampire_inference_rule_t_AVATAR_SPLIT_CLAUSE
            || rule == sys::vampire_inference_rule_t_AVATAR_CONTRADICTION_CLAUSE
            || rule == sys::vampire_inference_rule_t_AVATAR_REFUTATION
        {
            Self::Avatar
        } else {
            Self::Other
        }
    }
}

/// A single step in a [`Proof`].
///
/// Each step records:
/// - The [`Formula`] derived at this step ([`ProofStep::conclusion`])
/// - The [`ProofRule`] used to derive it ([`ProofStep::rule`])
/// - The indices (into [`Proof::steps`]) of the premises this step depends on
///   ([`ProofStep::premises`])
/// - A discovery-order counter assigned by Vampire ([`ProofStep::discovery_order`])
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProofStep {
    discovery_order: u32,
    rule: ProofRule,
    premises: Vec<usize>,
    conclusion: Formula,
    axiom_index: Option<usize>,
    axiom_name: Option<String>,
}

impl ProofStep {
    /// Returns the formula derived at this step.
    pub fn conclusion(&self) -> Formula {
        self.conclusion
    }

    /// Returns the inference rule used to derive this step.
    pub fn rule(&self) -> ProofRule {
        self.rule
    }

    /// Returns the indices of the premises this step was derived from.
    ///
    /// Each value is an index into the [`Proof::steps`] slice (i.e. the position
    /// of the premise among the steps that actually appear in the proof, not its
    /// [`ProofStep::discovery_order`]).
    pub fn premises(&self) -> &[usize] {
        &self.premises
    }

    /// Returns Vampire's internal discovery-order ID for this step.
    ///
    /// As Vampire searches for a proof it assigns every derived fact a
    /// monotonically increasing numeric ID. When the proof is extracted, only
    /// the facts that were actually *used* in the refutation are included, so
    /// there may be gaps in the sequence. The steps in [`Proof::steps`] are
    /// sorted by this value, which also gives a valid topological ordering of
    /// the proof DAG.
    pub fn discovery_order(&self) -> u32 {
        self.discovery_order
    }

    /// For a step that is one of the problem's input axioms: the axiom's index
    /// in the order it was added ([`Problem::with_axiom`] /
    /// [`Problem::with_named_axiom`]). `None` for every other step, including
    /// the negated conjecture.
    pub fn axiom_index(&self) -> Option<usize> {
        self.axiom_index
    }

    /// For a step that is an input axiom added with
    /// [`Problem::with_named_axiom`]: that name. `None` otherwise.
    pub fn axiom_name(&self) -> Option<&str> {
        self.axiom_name.as_deref()
    }
}

#[cfg(test)]
mod test {
    use super::{Function, Predicate, Problem, ProofRes, Term, exists, forall};
    use crate::Options;

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

    #[test]
    fn term_structural_equality() {
        let f = Function::new("f_teq", 2);
        let g = Function::new("g_teq", 1);

        // Same constant constructed twice: equal
        let a1 = Function::constant("a_teq");
        let a2 = Function::constant("a_teq");
        assert_eq!(a1, a2);

        // Different constants: not equal
        let b = Function::constant("b_teq");
        assert_ne!(a1, b);

        // Same compound term constructed twice: equal
        let t1 = f.with([g.with(a1), b]);
        let t2 = f.with([g.with(a1), b]);
        assert_eq!(t1, t2);

        // Different argument: not equal
        let t3 = f.with([g.with(b), b]);
        assert_ne!(t1, t3);

        // Same variable index: equal
        let x0a = Term::new_var(0);
        let x0b = Term::new_var(0);
        assert_eq!(x0a, x0b);

        // Different variable indices: not equal
        let x1 = Term::new_var(1);
        assert_ne!(x0a, x1);

        // Variable vs constant: not equal
        assert_ne!(x0a, a1);
    }

    #[test]
    fn term_structural_hash() {
        use std::collections::HashSet;

        let f = Function::new("f_thash", 2);
        let a = Function::constant("a_thash");
        let b = Function::constant("b_thash");

        let t1 = f.with([a, b]);
        let t2 = f.with([a, b]);
        let t3 = f.with([b, a]);

        // Equal terms hash identically (required by Hash contract)
        let mut set = HashSet::new();
        set.insert(t1);
        assert!(set.contains(&t2));

        // Different terms can be stored together
        set.insert(t3);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn formula_structural_equality() {
        let p = Predicate::new("p_feq", 1);
        let q = Predicate::new("q_feq", 1);
        let a = Function::constant("a_feq");
        let b = Function::constant("b_feq");

        // Same atomic formula constructed twice: equal
        let pa1 = p.with(a);
        let pa2 = p.with(a);
        assert_eq!(pa1, pa2);

        // Different predicates: not equal
        assert_ne!(p.with(a), q.with(a));

        // Different arguments: not equal
        assert_ne!(p.with(a), p.with(b));

        // Negation: equal iff inner equal
        assert_eq!(!pa1, !pa2);
        assert_ne!(!pa1, !p.with(b));

        // Conjunction
        let f1 = p.with(a) & q.with(b);
        let f2 = p.with(a) & q.with(b);
        let f3 = p.with(a) & q.with(a);
        assert_eq!(f1, f2);
        assert_ne!(f1, f3);

        // Implication
        let i1 = p.with(a) >> q.with(b);
        let i2 = p.with(a) >> q.with(b);
        assert_eq!(i1, i2);
        // Implication is not symmetric
        assert_ne!(p.with(a) >> q.with(b), q.with(b) >> p.with(a));

        // A formula is equal to itself (Copy type, same variable index)
        let fa = forall(|x| p.with(x));
        assert_eq!(fa, fa);

        // forall vs exists with same body: not equal (different connective)
        let fe = exists(|x| p.with(x));
        assert_ne!(fa, fe);

        // Equality literals: same args → equal
        let eq1 = a.eq(b);
        let eq2 = a.eq(b);
        assert_eq!(eq1, eq2);
        // Equality literal vs inequality literal: not equal
        assert_ne!(a.eq(b), !p.with(a));
    }

    #[test]
    fn formula_structural_hash() {
        use std::collections::HashSet;

        let p = Predicate::new("p_fhash", 1);
        let q = Predicate::new("q_fhash", 1);
        let a = Function::constant("a_fhash");

        let f1 = p.with(a) & q.with(a);
        let f2 = p.with(a) & q.with(a);
        let f3 = p.with(a) | q.with(a);

        let mut set = HashSet::new();
        set.insert(f1);
        // Equal formula is found in the set
        assert!(set.contains(&f2));
        // Different formula can be added
        set.insert(f3);
        assert_eq!(set.len(), 2);
    }

    // TFF tests

    #[test]
    fn tff_sort_idempotent() {
        // Registering the same sort twice must return the same index.
        let s1 = super::Sort::new("tff_sort_idem_s");
        let s2 = super::Sort::new("tff_sort_idem_s");
        assert_eq!(s1, s2);
    }

    #[test]
    fn tff_typed_function_idempotent() {
        // Registering the same typed function twice must return the same symbol.
        let s = super::Sort::new("tff_fn_idem_sort");
        let f1 = Function::typed("tff_fn_idem_f", &[s.clone()], s.clone());
        let f2 = Function::typed("tff_fn_idem_f", &[s.clone()], s);
        assert_eq!(f1, f2);
    }

    #[test]
    fn tff_typed_predicate_idempotent() {
        let s = super::Sort::new("tff_pred_idem_sort");
        let p1 = Predicate::typed("tff_pred_idem_p", &[s.clone()]);
        let p2 = Predicate::typed("tff_pred_idem_p", &[s]);
        assert_eq!(p1, p2);
    }

    #[test]
    fn tff_socrates_typed() {
        // TFF version of the Socrates syllogism using a user-defined sort.
        let person = super::Sort::new("person_tff");

        let is_mortal = Predicate::typed("mortal_tff", &[person.clone()]);
        let is_man = Predicate::typed("man_tff", &[person.clone()]);
        let socrates = Function::typed("socrates_tff", &[], person.clone()).with(());

        let men_are_mortal =
            super::forall_typed(person, |x| is_man.with(x) >> is_mortal.with(x));

        let result = Problem::new(Options::new())
            .with_axiom(is_man.with(socrates))
            .with_axiom(men_are_mortal)
            .conjecture(is_mortal.with(socrates))
            .solve();

        assert_eq!(result, ProofRes::Proved);
    }

    #[test]
    fn tff_typed_equality() {
        // Prove that if father_of(x) = father_of(y) and x = alice then
        // father_of(alice) = father_of(y), using typed equality.

        let person = super::Sort::new("person_eq_tff");
        let father_of = Function::typed("father_of_tff", &[person.clone()], person.clone());
        let alice = Function::typed("alice_tff", &[], person.clone()).with(());

        let result = Problem::new(Options::new())
            .with_axiom(super::forall_typed(person.clone(), |x| {
                super::forall_typed(person.clone(), |y| {
                    father_of.with(x).typed_eq(father_of.with(y), person.clone())
                        >> father_of.with(alice).typed_eq(father_of.with(y), person.clone())
                })
            }))
            .conjecture(
                father_of
                    .with(alice)
                    .typed_eq(father_of.with(alice), person),
            )
            .solve();

        assert_eq!(result, ProofRes::Proved);
    }

    #[test]
    fn tff_builtin_sorts_accessible() {
        // Smoke test: built-in sorts return valid, distinct indices.
        let i = super::Sort::default_sort();
        let z = super::Sort::int();
        let r = super::Sort::real();
        let q = super::Sort::rational();
        // All should be distinct from each other.
        assert_ne!(i, z);
        assert_ne!(i, r);
        assert_ne!(i, q);
        assert_ne!(z, r);
        assert_ne!(z, q);
        assert_ne!(r, q);
    }

    #[test]
    fn tff_to_tptp_fof_problem() {
        // FOF problem: to_tptp() should emit fof(...) syntax.
        let p = Predicate::new("p_fof_tptp", 1);
        let x = Function::constant("a_fof_tptp");
        let mut problem = Problem::new(Options::new());
        problem.with_axiom(p.with(x));
        problem.conjecture(p.with(x));
        let tptp = problem.to_tptp();
        assert!(tptp.contains("fof(axiom_0, axiom,"), "Expected fof keyword, got: {}", tptp);
        assert!(tptp.contains("fof(conjecture, conjecture,"), "Expected conjecture, got: {}", tptp);
    }

    #[test]
    fn tff_to_tptp_tff_problem() {
        // TFF problem: to_tptp() should emit tff(...) syntax with type declarations.
        let list = super::Sort::new("list_to_tptp");
        let nil = Function::typed("nil_to_tptp", &[], list.clone());
        let sorted = Predicate::typed("sorted_to_tptp", &[list.clone()]);

        let mut problem = Problem::new_tff(Options::new());
        problem.declare_sort(list.clone());
        problem.declare_function(nil.clone());
        problem.declare_predicate(sorted.clone());
        problem.with_axiom(sorted.with(nil.with(())));
        problem.conjecture(sorted.with(nil.with(())));

        let tptp = problem.to_tptp();
        assert!(tptp.contains("tff(sort_list_to_tptp, type,"), "Missing sort decl: {}", tptp);
        assert!(tptp.contains("tff(fn_nil_to_tptp,"), "Missing function decl: {}", tptp);
        assert!(tptp.contains("tff(pred_sorted_to_tptp_"), "Missing predicate decl: {}", tptp);
        assert!(tptp.contains("tff(axiom_0, axiom,"), "Expected tff axiom: {}", tptp);
        assert!(tptp.contains("tff(conjecture, conjecture,"), "Expected tff conjecture: {}", tptp);
    }

    #[test]
    fn tff_to_tptp_roundtrip() {
        // Parse a TPTP string, then emit it back and re-parse to confirm it round-trips.
        let input = "
            tff(list_type, type, list_rt: $tType).
            tff(nil_type, type, nil_rt: list_rt).
            tff(sorted_type, type, sorted_rt: list_rt > $o).
            tff(empty_sorted, axiom, sorted_rt(nil_rt)).
            tff(check, conjecture, sorted_rt(nil_rt)).
        ";
        let mut p1 = Problem::from_tptp(input).unwrap();
        assert_eq!(p1.solve(), ProofRes::Proved);

        let tptp_out = p1.to_tptp();
        assert!(tptp_out.contains("tff(sort_list_rt, type,"), "Missing sort decl in output: {}", tptp_out);

        let mut p2 = Problem::from_tptp(&tptp_out).unwrap();
        assert_eq!(p2.solve(), ProofRes::Proved);
    }
}
