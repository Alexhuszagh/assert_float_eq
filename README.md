assert_float_eq
===============

[![Build Status](https://api.travis-ci.org/Alexhuszagh/assert_float_eq.svg?branch=master)](https://travis-ci.org/Alexhuszagh/assert_float_eq)
[![Latest Version](https://img.shields.io/crates/v/assert_float_eq.svg)](https://crates.io/crates/assert_float_eq)

Assertions to check floating-point equality within a user-defined tolerance. Works in both a `std` and `no_std` context.

**Table Of Contents**

- [Getting Started](#getting-started)
- [Description](#description)
- [Documentation](#documentation)
- [License](#license)
- [Contributing](#contributing)

# Getting Started

First, add assert_float_eq to your `Cargo.toml`:

```yaml
[dependencies]
assert_float_eq = "1.0"
```

Next, import the macros in `lib.rs`:

```rust
#[macro_use]
extern crate assert_float_eq;
```

Finally, use the assertions like any other rust assertions:

```rust
assert_float_absolute_eq!(3.0, 4.0, 1.0);
assert_float_relative_eq!(4.0, 3.9, 0.03);
assert_f32_near!(1.0e-45, 7.0e-45, 4);
assert_f64_near!(5.0e-324, 2.5e-323, 4);
```

# Description

assert_float_eq exports 4 macros, each of which provides a different heuristic for comparing floating-point numbers.

`assert_float_absolute_eq` compares to values such that the absolute value of the difference between the floats is less than epsilon (default 1e-6), or `| a - b | < epsilon`. This is the easiest-to-understand macro, since it ensures the difference between two floats is below some fixed threshold. However, for very small or very large floats, absolute comparisons can lead to fault comparisons, due to the extremely high or low precision of floating point numbers at extremes, respectively.

`assert_float_relative_eq` compares to values such that the relative value of the difference between the floats is less than epsilon (default 1e-6), or `(| a - b | / max(|a|, |b|)` < epsilon`. This is another easy-to-understand macro, and works well with large floats, however, it fails for small (denormal) floats, especially 0.

`assert_f32_near` and `assert_f64_near` ensure two floats are within a number of steps of each other, by default, 4. This allows for a scaling precision for all values of floats, however, it may counter-intuitive due to the extremely high precision for small floats and low precision for large floats. For example, for a 32-bit float, it takes ~1e9 steps to go from 0.0 to 1e-6, however, each step for a float with a value of 3e37 increments the float by ~3e30.

# Documentation

assert_float_eq's documentation can be found on [docs.rs](https://docs.rs/assert_float_eq).

# License

assert_float_eq is dual licensed under the Apache 2.0 license as well as the MIT license. See the LICENCE-MIT and the LICENCE-APACHE files for the licenses.

# Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in assert_float_eq by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
