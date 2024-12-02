//! Assertions that two floating point numbers are approximately equal.
//!
//! Floating-point equality is difficult, and therefore numerous macros
//! are provided. At the most simple, [`assert_float_absolute_eq`] and
//! [`assert_float_relative_eq`] assert that the difference between two
//! floats is smaller than epsilon (default 1e-6) absolutely or
//! relatively, respectively.
//!
//! However, due to the decreasing precision of floating-point numbers
//! at large values, and the desire for high-stringency, macros to detect
//! whether a floating point is within a number of "steps" of another
//! are provided. [`assert_f32_near`] and [`assert_f64_near`] assert whether
//! an f32 or f64 is within n "steps" (default 4) of another, respectively.
//! A floating-point step is an increment to the bit-wise pattern of the
//! float, for example, if a float is represented in-memory as `0x0000FFFF`,
//! then the next float would be `0x00010000`. This allows float equality
//! comparisons to floating-point numbers at any precision, simplifying
//! equality checks for extremely high or low floats without sacrificing
//! accuracy.
//!
//! For example, for a 32-bit float of value `3e37`, each step is `~4e30`,
//! a gargantuan value (but only a small fraction, ~0.00001% of the total
//! value).
//!
//! In addition to the `assert_*` macros, which panic if the condition
//! is not true, assert_float_eq also has `expect_*` macros, which
//! return a `Result<(), T: Display>`, when panicking is not desirable.
//!
//! [`assert_float_absolute_eq`]: macro.assert_float_absolute_eq.html
//! [`assert_float_relative_eq`]: macro.assert_float_relative_eq.html
//! [`assert_f64_near`]: macro.assert_f64_near.html
//! [`assert_f32_near`]: macro.assert_f32_near.html

use core::fmt::{Debug, Display, Formatter, Result as FmtResult};

// IMPLEMENTATION

// Make sure we export all functions so they can be visible
// outside of the crate.

// F32

// IEEE754 CONSTANTS
// 32 bit floats have the following representation:
// Sign:        10000000000000000000000000000000
// Exponent:    01111111100000000000000000000000
// Hidden:      00000000100000000000000000000000
// Fraction:    00000000011111111111111111111111
const U32_SIGN_MASK: u32 = 0x80000000;
const U32_EXPONENT_MASK: u32 = 0x7F800000;
const U32_HIDDEN_BIT: u32 = 0x00800000;
const U32_SIGNIFICAND_MASK: u32 = 0x007FFFFF;
const U32_INFINITY: u32 = 0x7F800000;

/// Check if value is denormal, has leading zeros in significand.
#[inline]
#[doc(hidden)]
pub fn is_denormal_f32(f: f32) -> bool {
    let u = f.to_bits();
    (u & U32_EXPONENT_MASK) == 0
}

/// Get the sign of a 64-bit float.
#[inline]
#[doc(hidden)]
pub fn sign_f32(f: f32) -> i32 {
    let u = f.to_bits();
    if (u & U32_SIGN_MASK) == 0 {
        1
    } else {
        -1
    }
}

/// Get the significand of a 32-bit float.
#[inline]
#[doc(hidden)]
pub fn significand_f32(f: f32) -> u32 {
    let u = f.to_bits();
    let s = u & U32_SIGNIFICAND_MASK;
    if is_denormal_f32(f) {
        s
    } else {
        s + U32_HIDDEN_BIT
    }
}

/// Get the next 32-bit float.
#[inline]
#[doc(hidden)]
pub fn next_f32(f: f32) -> f32 {
    let u = f.to_bits();
    if u == U32_INFINITY {
        f32::from_bits(U32_INFINITY)
    } else if sign_f32(f) < 0 && significand_f32(f) == 0 {
        0.0
    } else if sign_f32(f) < 0 {
        f32::from_bits(u - 1)
    } else {
        f32::from_bits(u + 1)
    }
}

/// Get the next N steps from a 32-bit float.
#[inline]
#[doc(hidden)]
pub fn next_n_f32(mut f: f32, n: u32) -> f32 {
    for _ in 0..n {
        f = next_f32(f);
    }
    f
}

/// Get the previous 32-bit float.
#[inline]
#[doc(hidden)]
pub fn previous_f32(f: f32) -> f32 {
    let u = f.to_bits();
    if u == (U32_INFINITY | U32_SIGN_MASK) {
        -f32::from_bits(U32_INFINITY)
    } else if sign_f32(f) < 0 {
        f32::from_bits(u + 1)
    } else if significand_f32(f) == 0 {
        -0.0
    } else {
        f32::from_bits(u - 1)
    }
}

/// Get the previous N steps from a 32-bit float.
#[inline]
#[doc(hidden)]
pub fn previous_n_f32(mut f: f32, n: u32) -> f32 {
    for _ in 0..n {
        f = previous_f32(f);
    }
    f
}

// F64

// IEEE754 CONSTANTS
// 64 bit floats have the following representation:
// Sign:        1000000000000000000000000000000000000000000000000000000000000000
// Exponent:    0111111111110000000000000000000000000000000000000000000000000000
// Hidden:      0000000000010000000000000000000000000000000000000000000000000000
// Significand: 0000000000001111111111111111111111111111111111111111111111111111
const U64_SIGN_MASK: u64 = 0x8000000000000000;
const U64_EXPONENT_MASK: u64 = 0x7FF0000000000000;
const U64_HIDDEN_BIT: u64 = 0x0010000000000000;
const U64_SIGNIFICAND_MASK: u64 = 0x000FFFFFFFFFFFFF;
const U64_INFINITY: u64 = 0x7FF0000000000000;

/// Check if value is denormal, has leading zeros in significand.
#[inline]
#[doc(hidden)]
pub fn is_denormal_f64(f: f64) -> bool {
    let u = f.to_bits();
    (u & U64_EXPONENT_MASK) == 0
}

/// Get the sign of a 64-bit float.
#[inline]
#[doc(hidden)]
pub fn sign_f64(f: f64) -> i32 {
    let u = f.to_bits();
    if (u & U64_SIGN_MASK) == 0 {
        1
    } else {
        -1
    }
}

/// Get the significand of a 64-bit float.
#[inline]
#[doc(hidden)]
pub fn significand_f64(f: f64) -> u64 {
    let u = f.to_bits();
    let s = u & U64_SIGNIFICAND_MASK;
    if is_denormal_f64(f) {
        s
    } else {
        s + U64_HIDDEN_BIT
    }
}

/// Get the next 64-bit float.
#[inline]
#[doc(hidden)]
pub fn next_f64(f: f64) -> f64 {
    let u = f.to_bits();
    if u == U64_INFINITY {
        f64::from_bits(U64_INFINITY)
    } else if sign_f64(f) < 0 && significand_f64(f) == 0 {
        0.0
    } else if sign_f64(f) < 0 {
        f64::from_bits(u - 1)
    } else {
        f64::from_bits(u + 1)
    }
}

/// Get the next N steps from a 64-bit float.
#[inline]
#[doc(hidden)]
pub fn next_n_f64(mut f: f64, n: u32) -> f64 {
    for _ in 0..n {
        f = next_f64(f);
    }
    f
}

/// Get the previous 64-bit float.
#[inline]
#[doc(hidden)]
pub fn previous_f64(f: f64) -> f64 {
    let u = f.to_bits();
    if u == (U64_INFINITY | U64_SIGN_MASK) {
        -f64::from_bits(U64_INFINITY)
    } else if sign_f64(f) < 0 {
        f64::from_bits(u + 1)
    } else if significand_f64(f) == 0 {
        -0.0
    } else {
        f64::from_bits(u - 1)
    }
}

/// Get the previous N steps from a 64-bit float.
#[inline]
#[doc(hidden)]
pub fn previous_n_f64(mut f: f64, n: u32) -> f64 {
    for _ in 0..n {
        f = previous_f64(f);
    }
    f
}

// GENERAL

/// Message for absolute errors.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_absolute_eq_error_msg {
    () => {
        "assertion failed: `|a-b| < epsilon` a: {:?}, b: {:?}, epsilon: {:?}"
    };
}

/// Message for absolute errors.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_absolute_ne_error_msg {
    () => {
        "assertion failed: `|a-b| >= epsilon` a: {:?}, b: {:?}, epsilon: {:?}"
    };
}

/// Message for relative errors.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_relative_eq_error_msg {
    () => {
        "assertion failed: `|(a-b) / a| < epsilon` a: {:?}, b: {:?}, epsilon: {:?}"
    };
}

/// Message for relative errors.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_relative_ne_error_msg {
    () => {
        "assertion failed: `|(a-b) / a| >= epsilon` a: {:?}, b: {:?}, epsilon: {:?}"
    };
}

/// Message for near errors.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_near_error_msg {
    () => ("assertion failed: `b is outside of n steps from a` a: {:?}, b: {:?}, n: {:?}, previous: {:?}, next: {:?}")
}

/// Message for far errors.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_far_error_msg {
    () => ("assertion failed: `b is within n steps from a` a: {:?}, b: {:?}, n: {:?}, previous: {:?}, next: {:?}")
}

/// Generate the classes for the threshold errors.
#[doc(hidden)]
macro_rules! threshold_error_impl {
    ($t:ident, $msg:expr) => {
        /// Error result for an error threshold.
        #[derive(Debug)]
        #[doc(hidden)]
        pub struct $t<Float: Debug> {
            a: Float,
            b: Float,
            epsilon: Float,
        }

        impl<Float: Debug> $t<Float> {
            pub fn new(a: Float, b: Float, epsilon: Float) -> Self {
                $t {
                    a,
                    b,
                    epsilon,
                }
            }
        }

        impl<Float: Debug> Display for $t<Float> {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                write!(f, $msg, self.a, self.b, self.epsilon)
            }
        }
    };
}

threshold_error_impl!(AbsoluteEqError, afe_absolute_eq_error_msg!());
threshold_error_impl!(AbsoluteNeError, afe_absolute_ne_error_msg!());
threshold_error_impl!(RelativeEqError, afe_relative_eq_error_msg!());
threshold_error_impl!(RelativeNeError, afe_relative_ne_error_msg!());

/// Error result for a the `expect_f*_near` methods.
#[derive(Debug)]
#[doc(hidden)]
pub struct FloatNearError<Float: Debug, Int: Debug> {
    a: Float,
    b: Float,
    n: Int,
    previous: Float,
    next: Float,
}

impl<Float: Debug, Int: Debug> FloatNearError<Float, Int> {
    pub fn new(a: Float, b: Float, n: Int, previous: Float, next: Float) -> Self {
        Self {
            a,
            b,
            n,
            previous,
            next,
        }
    }
}

impl<Float: Debug, Int: Debug> Display for FloatNearError<Float, Int> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, afe_near_error_msg!(), self.a, self.b, self.n, self.previous, self.next)
    }
}

/// Error result for a the `expect_f*_far` methods.
#[derive(Debug)]
#[doc(hidden)]
pub struct FloatFarError<Float: Debug, Int: Debug> {
    a: Float,
    b: Float,
    n: Int,
    previous: Float,
    next: Float,
}

impl<Float: Debug, Int: Debug> FloatFarError<Float, Int> {
    pub fn new(a: Float, b: Float, n: Int, previous: Float, next: Float) -> Self {
        Self {
            a,
            b,
            n,
            previous,
            next,
        }
    }
}

impl<Float: Debug, Int: Debug> Display for FloatFarError<Float, Int> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, afe_far_error_msg!(), self.a, self.b, self.n, self.previous, self.next)
    }
}

/// Convert a boolean and String to a result.
#[inline(always)]
#[doc(hidden)]
pub fn bool_to_result<T: Display>(r: bool, err: T) -> Result<(), T> {
    match r {
        true => Ok(()),
        false => Err(err),
    }
}

/// Maximum implementation.
///
/// Don't worry about propagating NaN, for our use-case, any NaN value
/// will remain after comparison and lead to a diagnostic error.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_max {
    ($a:expr, $b:expr) => {{
        let (a, b) = ($a, $b);
        if a < b {
            b
        } else {
            a
        }
    }};
}

/// Absolute value implementation.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_abs {
    ($f:expr) => {{
        let f = $f;
        if f < 0.0 {
            -f
        } else {
            f
        }
    }};
}

/// Returns true if the values are absolutely equal within a tolerance.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_is_absolute_eq {
    ($a:ident, $b:ident, $epsilon:ident) => {
        $crate::afe_abs!($a - $b) <= $epsilon
    };
}

/// Returns true if the values are relatively equal within a tolerance.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_is_relative_eq {
    ($a:ident, $b:ident, $epsilon:ident) => {
        if $a == 0.0 {
            $b == 0.0
        } else {
            // Only care about the magnitude, not the sign.
            let denom = $crate::afe_abs!($a);
            ($crate::afe_abs!($a - $b) / denom) <= $epsilon
        }
    };
}

/// Returns true if two 32-bit floats are within n steps of each other.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_is_f32_near {
    ($a:ident, $b:ident, $n:ident) => {{
        let previous = $crate::previous_n_f32($a, $n);
        let next = $crate::next_n_f32($a, $n);
        let r = $b >= previous && $b <= next;
        (r, previous, next)
    }};
}

/// Returns true if two 64-bit floats are within n steps of each other.
#[macro_export]
#[doc(hidden)]
macro_rules! afe_is_f64_near {
    ($a:ident, $b:ident, $n:ident) => {{
        let previous = $crate::previous_n_f64($a, $n);
        let next = $crate::next_n_f64($a, $n);
        let r = $b >= previous && $b <= next;
        (r, previous, next)
    }};
}

// API

// EXPECT

/// Expect the absolute error between two values is less than epsilon.
///
/// Returns an error if `| a - b | > epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Absolute error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::expect_float_absolute_eq;
/// # pub fn main() {
/// assert!(expect_float_absolute_eq!(3.0, 4.0, 1.0).is_ok());
/// assert!(expect_float_absolute_eq!(3.0, 4.0, 0.9).is_err());
/// assert!(expect_float_absolute_eq!(1.0, 0.5 + 0.5).is_ok());
/// # }
/// ```
#[macro_export]
macro_rules! expect_float_absolute_eq {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_absolute_eq!(a, b, eps);
        let e = $crate::AbsoluteEqError::new(a, b, eps);
        $crate::bool_to_result(r, e)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_float_absolute_eq!($a, $b, 1.0e-6)
    };
}

/// Expect the absolute error between two values is greater than epsilon.
///
/// Returns an error if `| a - b | <= epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Absolute error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::expect_float_absolute_ne;
/// # pub fn main() {
/// assert!(expect_float_absolute_ne!(3.0, 4.0, 1.0 + 1.0e-7).is_err());
/// assert!(expect_float_absolute_ne!(3.0, 4.0, 1.0 - 1.0e-7).is_ok());
/// # }
/// ```
#[macro_export]
macro_rules! expect_float_absolute_ne {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_absolute_eq!(a, b, eps);
        let e = $crate::AbsoluteNeError::new(a, b, eps);
        $crate::bool_to_result(!r, e)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_float_absolute_ne!($a, $b, 1.0e-6)
    };
}

/// Expect the relative error between two values is less than epsilon.
///
/// Returns an error if `|(a - b) / a| > epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Relative error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::expect_float_relative_eq;
/// # pub fn main() {
/// assert!(expect_float_relative_eq!(4.0, 3.0, 0.25).is_ok());
/// assert!(expect_float_relative_eq!(4.0, 3.0, 0.20).is_err());
/// assert!(expect_float_relative_eq!(1.0, 0.5 + 0.5).is_ok());
/// # }
/// ```
#[macro_export]
macro_rules! expect_float_relative_eq {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_relative_eq!(a, b, eps);
        let e = $crate::RelativeEqError::new(a, b, eps);
        $crate::bool_to_result(r, e)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_float_relative_eq!($a, $b, 1.0e-6)
    };
}

/// Expect the relative error between two values is greater than epsilon.
///
/// Returns an error if `|(a - b) / a| <= epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Relative error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::expect_float_relative_ne;
/// # pub fn main() {
/// assert!(expect_float_relative_ne!(4.0, 3.0, 0.25).is_err());
/// assert!(expect_float_relative_ne!(4.0, 3.0, 0.20).is_ok());
/// assert!(expect_float_relative_ne!(1.0, 0.5 + 0.5).is_err());
/// # }
/// ```
#[macro_export]
macro_rules! expect_float_relative_ne {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_relative_eq!(a, b, eps);
        let e = $crate::RelativeNeError::new(a, b, eps);
        $crate::bool_to_result(!r, e)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_float_relative_ne!($a, $b, 1.0e-6)
    };
}

/// Expect two 32-bit floats are within `n` steps of each other.
///
/// Returns an error if the two floats are more than `n` steps away
/// from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 1e-45 (`0x00000001`) would be
/// 3e-45 (`0x00000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::expect_f32_near;
/// # pub fn main() {
/// assert!(expect_f32_near!(1e-45, 7e-45).is_ok());
/// assert!(expect_f32_near!(1e-45, 1.4e-44, 9).is_ok());
/// assert!(expect_f32_near!(1e-45, 1.4e-44, 8).is_err());
/// assert!(expect_f32_near!(3e37, 3.000001e+37).is_ok());
/// # }
/// ```
#[macro_export]
macro_rules! expect_f32_near {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f32_near!(a, b, n);
        let e = $crate::FloatNearError::new(a, b, n, previous, next);
        $crate::bool_to_result(r, e)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_f32_near!($a, $b, 4)
    };
}

/// Expect two 32-bit floats are not within `n` steps of each other.
///
/// Returns an error if the two floats are less than or equal to `n`
/// steps away from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 1e-45 (`0x00000001`) would be
/// 3e-45 (`0x00000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::expect_f32_far;
/// # pub fn main() {
/// assert!(expect_f32_far!(1e-45, 7e-45).is_err());
/// assert!(expect_f32_far!(1e-45, 1.4e-44, 9).is_err());
/// assert!(expect_f32_far!(1e-45, 1.4e-44, 8).is_ok());
/// assert!(expect_f32_far!(3e37, 3.000001e+37).is_err());
/// # }
/// ```
#[macro_export]
macro_rules! expect_f32_far {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f32_near!(a, b, n);
        let e = $crate::FloatFarError::new(a, b, n, previous, next);
        $crate::bool_to_result(!r, e)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_f32_far!($a, $b, 4)
    };
}

/// Expect two 64-bit floats are within `n` steps of each other.
///
/// Returns an error if the two floats are more than `n` steps away
/// from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 1e-45 (`0x00000001`) would be
/// 3e-45 (`0x00000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::expect_f64_near;
/// # pub fn main() {
/// assert!(expect_f64_near!(5e-324, 2.5e-323).is_ok());
/// assert!(expect_f64_near!(5e-324, 2.5e-323, 3).is_err());
/// assert!(expect_f64_near!(5e-324, 5e-323, 9).is_ok());
/// assert!(expect_f64_near!(5e-324, 5e-323, 8).is_err());
/// assert!(expect_f64_near!(3e300, 3.0000000000000025e+300).is_ok());
/// # }
/// ```
#[macro_export]
macro_rules! expect_f64_near {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f64_near!(a, b, n);
        let e = $crate::FloatNearError::new(a, b, n, previous, next);
        $crate::bool_to_result(r, e)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_f64_near!($a, $b, 4)
    };
}

/// Expect two 64-bit floats are not within `n` steps of each other.
///
/// Returns an error if the two floats are less than or equal to `n`
/// steps away from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 1e-45 (`0x00000001`) would be
/// 3e-45 (`0x00000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::expect_f64_far;
/// # pub fn main() {
/// assert!(expect_f64_far!(5e-324, 2.5e-323).is_err());
/// assert!(expect_f64_far!(5e-324, 2.5e-323, 3).is_ok());
/// assert!(expect_f64_far!(5e-324, 5e-323, 9).is_err());
/// assert!(expect_f64_far!(5e-324, 5e-323, 8).is_ok());
/// assert!(expect_f64_far!(3e300, 3.0000000000000025e+300).is_err());
/// # }
/// ```
#[macro_export]
macro_rules! expect_f64_far {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f64_near!(a, b, n);
        let e = $crate::FloatFarError::new(a, b, n, previous, next);
        $crate::bool_to_result(!r, e)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::expect_f64_far!($a, $b, 4)
    };
}

// ASSERT

/// Assert the absolute error between two values is less than epsilon.
///
/// Panics if `| a - b | > epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Absolute error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::assert_float_absolute_eq;
/// # pub fn main() {
/// assert_float_absolute_eq!(3.0, 4.0, 1.0);
/// assert_float_absolute_eq!(3.0, 4.0, 1.0 + 1.0e-7);
/// assert_float_absolute_eq!(1.0, 0.5 + 0.5);
/// assert_float_absolute_eq!(1.0, 0.5 + 0.5 + 1.0e-7);
/// assert_float_absolute_eq!(1.0, 0.5 + 0.5 - 1.0e-7);
/// # }
/// ```
#[macro_export]
macro_rules! assert_float_absolute_eq {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_absolute_eq!(a, b, eps);
        assert!(r, $crate::afe_absolute_eq_error_msg!(), a, b, eps)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_float_absolute_eq!($a, $b, 1.0e-6)
    };
}

/// Assert the absolute error between two values is greater than epsilon.
///
/// Panics if `| a - b | <= epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Absolute error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::assert_float_absolute_ne;
/// # pub fn main() {
/// assert_float_absolute_ne!(3.0, 4.0, 0.99);
/// assert_float_absolute_ne!(1.0, 0.5 + 0.499);
/// # }
/// ```
#[macro_export]
macro_rules! assert_float_absolute_ne {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_absolute_eq!(a, b, eps);
        assert!(!r, $crate::afe_absolute_ne_error_msg!(), a, b, eps)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_float_absolute_ne!($a, $b, 1.0e-6)
    };
}

/// Assert the relative error between two values is less than epsilon.
///
/// Panics if `|(a - b) / a| > epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Relative error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::assert_float_relative_eq;
/// # pub fn main() {
/// assert_float_relative_eq!(4.0, 3.0, 0.25);
/// assert_float_relative_eq!(1.0, 0.5 + 0.5);
/// # }
/// ```
#[macro_export]
macro_rules! assert_float_relative_eq {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_relative_eq!(a, b, eps);
        assert!(r, $crate::afe_relative_eq_error_msg!(), a, b, eps)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_float_relative_eq!($a, $b, 1.0e-6)
    };
}

/// Assert the relative error between two values is greater than epsilon.
///
/// Panics if `|(a - b) / a| <= epsilon`.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `epsilon` - Relative error tolerance between floats (defaults to
///   `1.0e-6`).
///
/// # Examples
///
/// ```
/// # use assert_float_eq::assert_float_relative_ne;
/// # pub fn main() {
/// assert_float_relative_ne!(4.0, 3.0, 0.25 - 1.0e-7);
/// assert_float_relative_ne!(1.0, 0.5 + 0.5 + 1e-5);
/// # }
/// ```
#[macro_export]
macro_rules! assert_float_relative_ne {
    // Explicit epsilon, fail.
    ($a:expr, $b:expr, $epsilon:expr) => {{
        let (a, b, eps) = ($a, $b, $epsilon);
        let r = $crate::afe_is_relative_eq!(a, b, eps);
        assert!(!r, $crate::afe_relative_ne_error_msg!(), a, b, eps)
    }};
    // No explicit epsilon, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_float_relative_ne!($a, $b, 1.0e-6)
    };
}

/// Assert two 32-bit floats are within `n` steps of each other.
///
/// Panics if the two floats are more than `n` steps away from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 1e-45 (`0x00000001`) would be
/// 3e-45 (`0x00000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::assert_f32_near;
/// # pub fn main() {
/// assert_f32_near!(1e-45, 7e-45);
/// assert_f32_near!(1e-45, 1.4e-44, 9);
/// assert_f32_near!(3e37, 3.000001e+37);
/// # }
/// ```
#[macro_export]
macro_rules! assert_f32_near {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f32_near!(a, b, n);
        assert!(r, $crate::afe_near_error_msg!(), a, b, n, previous, next)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_f32_near!($a, $b, 4)
    };
}

/// Assert two 32-bit floats are not within `n` steps of each other.
///
/// Panics if the two floats are less than or equal to `n` steps away
/// from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 1e-45 (`0x00000001`) would be
/// 3e-45 (`0x00000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::assert_f32_far;
/// # pub fn main() {
/// assert_f32_far!(1e-45, 8e-45);
/// assert_f32_far!(1e-45, 1.4e-44, 8);
/// assert_f32_far!(3e37, 3.0000014e+37);
/// # }
/// ```
#[macro_export]
macro_rules! assert_f32_far {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f32_near!(a, b, n);
        assert!(!r, $crate::afe_far_error_msg!(), a, b, n, previous, next)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_f32_far!($a, $b, 4)
    };
}

/// Assert two 64-bit floats are within `n` steps of each other.
///
/// Panics if the two floats are more than `n` steps away from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 5.e-324 (`0x0000000000000001`) would be
/// 1.e-323 (`0x0000000000000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::assert_f64_near;
/// # pub fn main() {
/// assert_f64_near!(5e-324, 2.5e-323);
/// assert_f64_near!(5e-324, 5e-323, 9);
/// assert_f64_near!(3e300, 3.0000000000000025e+300);
/// # }
/// ```
#[macro_export]
macro_rules! assert_f64_near {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f64_near!(a, b, n);
        assert!(r, $crate::afe_near_error_msg!(), a, b, n, previous, next)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_f64_near!($a, $b, 4)
    };
}

/// Assert two 64-bit floats are not within `n` steps of each other.
///
/// Panics if the two floats are less than or equal to `n` steps away
/// from each other.
///
/// * `a`       - First float.
/// * `b`       - Second float.
/// * `n`       - Step tolerance between floats (defaults to `4`).
///
/// Each step is derived from the previous float by incrementing
/// the float's bits, as if they were an integer, by 1.
/// For example, the next float from 5.e-324 (`0x0000000000000001`) would be
/// 1.e-323 (`0x0000000000000002`).
///
/// # Examples
///
/// ```rust
/// # use assert_float_eq::assert_f64_far;
/// # pub fn main() {
/// assert_f64_far!(5e-324, 3e-323);
/// assert_f64_far!(5e-324, 5.4e-323, 9);
/// assert_f64_far!(3e300, 3.000000000000007e+300);
/// # }
/// ```
#[macro_export]
macro_rules! assert_f64_far {
    // Explicit steps.
    ($a:expr, $b:expr, $n:expr) => {{
        let (a, b, n) = ($a, $b, $n);
        let (r, previous, next) = $crate::afe_is_f64_near!(a, b, n);
        assert!(!r, $crate::afe_far_error_msg!(), a, b, n, previous, next)
    }};
    // No explicit steps, use default.
    ($a:expr, $b:expr) => {
        $crate::assert_f64_far!($a, $b, 4)
    };
}

// TESTS
// -----

#[cfg(test)]
mod tests {
    #[test]
    #[should_panic]
    fn absolute_eq_fail() {
        assert_float_absolute_eq!(3.0, 4.0, 0.9);
    }

    #[test]
    fn absolute_eq_succeed() {
        assert_float_absolute_eq!(3.0, 4.0, 1.0);
    }

    #[test]
    #[should_panic]
    fn relative_eq_fail() {
        assert_float_relative_eq!(4.0, 3.0, 0.2);
    }

    #[test]
    fn relative_eq_succeed() {
        assert_float_relative_eq!(4.0, 3.0, 0.26);
    }

    #[test]
    #[should_panic]
    fn relative_eq_negative_zero_fail() {
        assert_float_relative_eq!(-0.1, 0.0);
    }

    #[test]
    #[should_panic]
    fn f32_near_fail() {
        assert_f32_near!(1.0e-45, 7.0e-45, 3);
    }

    #[test]
    fn f32_near_succeed() {
        assert_f32_near!(1.0e-45, 7.0e-45, 4);
    }

    #[test]
    #[should_panic]
    fn f64_near_fail() {
        assert_f64_near!(5.0e-324, 2.5e-323, 3);
    }

    #[test]
    #[should_panic]
    fn f64_far_fail() {
        assert_f64_far!(5.0e-324, 2.5e-323, 4);
    }

    #[test]
    fn f64_near_succeed() {
        assert_f64_near!(5.0e-324, 2.5e-323, 4);
    }

    #[test]
    fn f64_far_succeed() {
        assert_f64_far!(5.0e-324, 3e-323, 4);
    }
}
