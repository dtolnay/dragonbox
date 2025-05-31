// Translated from C++ to Rust. The original C++ code can be found at
// https://github.com/jk-jeon/dragonbox and carries the following license:
//
// Copyright 2020-2021 Junekey Jeon
//
// The contents of this file may be used under the terms of
// the Apache License v2.0 with LLVM Exceptions.
//
//    (See accompanying file LICENSE-Apache or copy at
//     https://llvm.org/foundation/relicensing/LICENSE.txt)
//
// Alternatively, the contents of this file may be used under the terms of
// the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE-Boost or copy at
//     https://www.boost.org/LICENSE_1_0.txt)
//
// Unless required by applicable law or agreed to in writing, this software
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.

//! [![github]](https://github.com/dtolnay/dragonbox)&ensp;[![crates-io]](https://crates.io/crates/dragonbox)&ensp;[![docs-rs]](https://docs.rs/dragonbox)
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [crates-io]: https://img.shields.io/badge/crates.io-fc8d62?style=for-the-badge&labelColor=555555&logo=rust
//! [docs-rs]: https://img.shields.io/badge/docs.rs-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs
//!
//! <br>
//!
//! This crate contains a basic port of <https://github.com/jk-jeon/dragonbox>
//! to Rust for benchmarking purposes.
//!
//! Please see the upstream repo for an explanation of the approach and
//! comparison to the Ryū algorithm.
//!
//! # Example
//!
//! ```
//! fn main() {
//!     let mut buffer = dragonbox::Buffer::new();
//!     let printed = buffer.format(1.234);
//!     assert_eq!(printed, "1.234E0");
//! }
//! ```
//!
//! ## Performance (lower is better)
//!
//! ![performance](https://raw.githubusercontent.com/dtolnay/dragonbox/master/performance.png)

#![no_std]
#![doc(html_root_url = "https://docs.rs/dragonbox/0.1.10")]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(
    clippy::bool_to_int_with_if,
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::comparison_chain,
    clippy::doc_markdown,
    clippy::expl_impl_clone_on_copy,
    clippy::if_not_else,
    clippy::items_after_statements,
    clippy::manual_range_contains,
    clippy::must_use_candidate,
    clippy::needless_doctest_main,
    clippy::never_loop,
    clippy::ptr_as_ptr,
    clippy::shadow_unrelated,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::toplevel_ref_arg,
    clippy::unreadable_literal,
    clippy::unusual_byte_groupings
)]

mod buffer;
mod cache;
mod div;
mod log;
mod to_chars;
mod wuint;

use crate::buffer::Sealed;
use crate::cache::EntryTypeExt as _;
use core::mem::MaybeUninit;

/// Buffer correctly sized to hold the text representation of any floating point
/// value.
///
/// ## Example
///
/// ```
/// let mut buffer = dragonbox::Buffer::new();
/// let printed = buffer.format_finite(1.234);
/// assert_eq!(printed, "1.234E0");
/// ```
pub struct Buffer {
    bytes: [MaybeUninit<u8>; to_chars::MAX_OUTPUT_STRING_LENGTH],
}

/// A floating point number that can be written into a
/// [`dragonbox::Buffer`][Buffer].
///
/// This trait is sealed and cannot be implemented for types outside of the
/// `dragonbox` crate.
pub trait Float: Sealed {}

// IEEE754-binary64
const SIGNIFICAND_BITS: usize = 52;
const EXPONENT_BITS: usize = 11;
const MIN_EXPONENT: i32 = -1022;
const EXPONENT_BIAS: i32 = -1023;

// Defines an unsigned integer type that is large enough
// to carry a variable of type f64.
// Most of the operations will be done on this integer type.
type CarrierUint = u64;

// Defines a signed integer type for holding significand bits together with the
// sign bit.
type SignedSignificand = i64;

// Number of bits in the above unsigned integer type.
const CARRIER_BITS: usize = 64;

// Extract exponent bits from a bit pattern. The result must be aligned to the
// LSB so that there is no additional zero paddings on the right. This function
// does not do bias adjustment.
const fn extract_exponent_bits(u: CarrierUint) -> u32 {
    const EXPONENT_BITS_MASK: u32 = (1 << EXPONENT_BITS) - 1;
    (u >> SIGNIFICAND_BITS) as u32 & EXPONENT_BITS_MASK
}

// Remove the exponent bits and extract significand bits together with the sign
// bit.
const fn remove_exponent_bits(u: CarrierUint, exponent_bits: u32) -> SignedSignificand {
    (u ^ ((exponent_bits as CarrierUint) << SIGNIFICAND_BITS)) as SignedSignificand
}

// Shift the obtained signed significand bits to the left by 1 to remove the
// sign bit.
const fn remove_sign_bit_and_shift(s: SignedSignificand) -> CarrierUint {
    (s as CarrierUint) << 1
}

const fn is_nonzero(u: CarrierUint) -> bool {
    (u << 1) != 0
}

const fn is_negative(s: SignedSignificand) -> bool {
    s < 0
}

const fn has_even_significand_bits(s: SignedSignificand) -> bool {
    s % 2 == 0
}

const fn compute_power32<const K: u32>(a: u32) -> u32 {
    // assert!(k >= 0);
    let mut p = 1;
    let mut i = 0;
    while i < K {
        p *= a;
        i += 1;
    }
    p
}

const fn compute_power64<const K: u32>(a: u64) -> u64 {
    // assert!(k >= 0);
    let mut p = 1;
    let mut i = 0;
    while i < K {
        p *= a;
        i += 1;
    }
    p
}

const fn count_factors<const A: usize>(mut n: usize) -> u32 {
    // assert!(a > 1);
    let mut c = 0;
    while n % A == 0 {
        n /= A;
        c += 1;
    }
    c
}

// Compute floor(n / 10^N) for small N.
// Precondition: n <= 2^a * 5^b (a = max_pow2, b = max_pow5)
fn divide_by_pow10<const N: u32, const MAX_POW2: i32, const MAX_POW5: i32>(n: u64) -> u64 {
    // Ensure no overflow.
    assert!(MAX_POW2 + (log::floor_log2_pow10(MAX_POW5) - MAX_POW5) < 64);

    // Specialize for 64-bit division by 1000.
    // Ensure that the correctness condition is met.
    if N == 3
        && MAX_POW2 + (log::floor_log2_pow10(N as i32 + MAX_POW5) - (N as i32 + MAX_POW5)) < 70
    {
        wuint::umul128_upper64(n, 0x8312_6e97_8d4f_df3c) >> 9
    } else {
        struct Divisor<const N: u32>;
        impl<const N: u32> Divisor<N> {
            const VALUE: u64 = compute_power64::<N>(10);
        }
        n / Divisor::<N>::VALUE
    }
}

struct Decimal {
    significand: u64,
    exponent: i32,
}

const KAPPA: u32 = 2;

fn compute_normal_interval_case(
    two_fc: CarrierUint,
    exponent: i32,
    include_left_endpoint: bool,
    include_right_endpoint: bool,
) -> Decimal {
    //////////////////////////////////////////////////////////////////////
    // Step 1: Schubfach multiplier calculation
    //////////////////////////////////////////////////////////////////////

    // Compute k and beta.
    let minus_k = log::floor_log10_pow2(exponent) - KAPPA as i32;
    let ref cache = unsafe { cache::get(-minus_k) };
    let beta_minus_1 = exponent + log::floor_log2_pow10(-minus_k);

    // Compute zi and deltai.
    // 10^kappa <= deltai < 10^(kappa + 1)
    let deltai = compute_delta(cache, beta_minus_1);
    let two_fr = two_fc | 1;
    let z_result = compute_mul_with_parity(two_fr << beta_minus_1, cache);
    let zi = z_result.integer_part;

    //////////////////////////////////////////////////////////////////////
    // Step 2: Try larger divisor; remove trailing zeros if necessary
    //////////////////////////////////////////////////////////////////////

    const BIG_DIVISOR: u32 = compute_power32::<{ KAPPA + 1 }>(10);
    const SMALL_DIVISOR: u32 = compute_power32::<KAPPA>(10);

    // Using an upper bound on zi, we might be able to optimize the division
    // better than the compiler; we are computing zi / big_divisor here.
    let mut significand = divide_by_pow10::<
        { KAPPA + 1 },
        { SIGNIFICAND_BITS as i32 + KAPPA as i32 + 2 },
        { KAPPA as i32 + 1 },
    >(zi);
    let mut r = (zi - BIG_DIVISOR as u64 * significand) as u32;

    loop {
        if r < deltai {
            // Exclude the right endpoint if necessary.
            if r == 0 && !z_result.is_integer && !include_right_endpoint {
                significand -= 1;
                r = BIG_DIVISOR;
                break;
            }
        } else if r > deltai {
            break;
        } else {
            // r == deltai; compare fractional parts.
            let x_result = compute_mul_parity_only(two_fc - 1, cache, beta_minus_1);

            if !(x_result.parity || (x_result.is_integer && include_left_endpoint)) {
                break;
            }
        }

        return may_have_trailing_zeros(significand, minus_k + KAPPA as i32 + 1);
    }

    //////////////////////////////////////////////////////////////////////
    // Step 3: Find the significand with the smaller divisor
    //////////////////////////////////////////////////////////////////////

    significand *= 10;

    // Compute the decimal significand and handle rounding
    let mut dist = r - (deltai / 2) + (SMALL_DIVISOR / 2);
    let approx_y_parity = ((dist ^ (SMALL_DIVISOR / 2)) & 1) != 0;

    // Is dist divisible by 10^kappa?

    let divisible_by_small_divisor = div::check_divisibility_and_divide_by_pow10(&mut dist);

    // Add dist / 10^kappa to the significand.
    significand += dist as CarrierUint;

    if divisible_by_small_divisor {
        // Check z^(f) >= epsilon^(f)
        // We have either yi == zi - epsiloni or yi == (zi - epsiloni) - 1,
        // where yi == zi - epsiloni if and only if z^(f) >= epsilon^(f)
        // Since there are only 2 possibilities, we only need to care about the parity.
        // Also, zi and r should have the same parity since the divisor
        // is an even number.
        let y_result = compute_mul_parity_only(two_fc, cache, beta_minus_1);
        if y_result.parity != approx_y_parity {
            significand -= 1;
        } else {
            // If z^(f) >= epsilon^(f), we might have a tie
            // when z^(f) == epsilon^(f), or equivalently, when y is an integer.
            // For tie-to-up case, we can just choose the upper one.
            if prefer_round_down(significand) && y_result.is_integer {
                significand -= 1;
            }
        }
    }

    no_trailing_zeros(significand, minus_k + KAPPA as i32)
}

fn compute_nearest_shorter(exponent: i32) -> Decimal {
    // Compute k and beta.
    let minus_k = log::floor_log10_pow2_minus_log10_4_over_3(exponent);
    let beta_minus_1 = exponent + log::floor_log2_pow10(-minus_k);

    // Compute xi and zi.
    let ref cache = unsafe { cache::get(-minus_k) };

    let mut xi = compute_left_endpoint_for_shorter_interval_case(cache, beta_minus_1);
    let zi = compute_right_endpoint_for_shorter_interval_case(cache, beta_minus_1);

    // If the left endpoint is not an integer, increase it.
    if !is_left_endpoint_integer_shorter_interval(exponent) {
        xi += 1;
    }

    // Try bigger divisor.
    let mut significand = zi / 10;

    // If succeed, remove trailing zeros if necessary and return.
    if significand * 10 >= xi {
        return may_have_trailing_zeros(significand, minus_k + 1);
    }

    // Otherwise, compute the round-up of y.
    significand = compute_round_up_for_shorter_interval_case(cache, beta_minus_1);

    // When tie occurs, choose one of them according to the rule.
    const SHORTER_INTERVAL_TIE_LOWER_THRESHOLD: i32 =
        -log::floor_log5_pow2_minus_log5_3(SIGNIFICAND_BITS as i32 + 4)
            - 2
            - SIGNIFICAND_BITS as i32;
    const SHORTER_INTERVAL_TIE_UPPER_THRESHOLD: i32 =
        -log::floor_log5_pow2(SIGNIFICAND_BITS as i32 + 2) - 2 - SIGNIFICAND_BITS as i32;

    if prefer_round_down(significand)
        && exponent >= SHORTER_INTERVAL_TIE_LOWER_THRESHOLD
        && exponent <= SHORTER_INTERVAL_TIE_UPPER_THRESHOLD
    {
        significand -= 1;
    } else if significand < xi {
        significand += 1;
    }

    no_trailing_zeros(significand, minus_k)
}

fn compute_mul_with_parity(u: CarrierUint, cache: &cache::EntryType) -> MultiplyResult {
    let r = wuint::umul192_upper128(u, *cache);
    let integer_part = (r >> 64) as u64;
    let is_integer = (r as u64) == 0;
    MultiplyResult {
        integer_part,
        is_integer,
    }
}

fn compute_delta(cache: &cache::EntryType, beta_minus_1: i32) -> u32 {
    (cache.high() >> ((CARRIER_BITS - 1) as i32 - beta_minus_1)) as u32
}

fn compute_mul_parity_only(
    two_f: CarrierUint,
    cache: &cache::EntryType,
    beta_minus_1: i32,
) -> ParityResult {
    debug_assert!(beta_minus_1 >= 1);
    debug_assert!(beta_minus_1 < 64);
    let r = wuint::umul192_lower128(two_f, *cache);
    let r_high = (r >> 64) as u64;
    let r_low = r as u64;
    let parity = ((r_high >> (64 - beta_minus_1)) & 1) != 0;
    let is_integer = ((r_high << beta_minus_1) | (r_low >> (64 - beta_minus_1))) == 0;
    ParityResult { parity, is_integer }
}

fn compute_left_endpoint_for_shorter_interval_case(
    cache: &cache::EntryType,
    beta_minus_1: i32,
) -> CarrierUint {
    (cache.high() - (cache.high() >> (SIGNIFICAND_BITS + 2)))
        >> ((CARRIER_BITS - SIGNIFICAND_BITS - 1) as i32 - beta_minus_1)
}

fn compute_right_endpoint_for_shorter_interval_case(
    cache: &cache::EntryType,
    beta_minus_1: i32,
) -> CarrierUint {
    (cache.high() + (cache.high() >> (SIGNIFICAND_BITS + 2)))
        >> ((CARRIER_BITS - SIGNIFICAND_BITS - 1) as i32 - beta_minus_1)
}

fn compute_round_up_for_shorter_interval_case(
    cache: &cache::EntryType,
    beta_minus_1: i32,
) -> CarrierUint {
    ((cache.high() >> ((CARRIER_BITS - SIGNIFICAND_BITS - 2) as i32 - beta_minus_1)) + 1) / 2
}

const fn floor_log2(mut n: u64) -> i32 {
    let mut count = -1;
    while n != 0 {
        count += 1;
        n >>= 1;
    }
    count
}

#[inline(always)]
fn prefer_round_down(decimal_significand: u64) -> bool {
    // For simplicity, implement to_even strategy
    decimal_significand % 2 != 0
}

fn is_left_endpoint_integer_shorter_interval(exponent: i32) -> bool {
    const CASE_SHORTER_INTERVAL_LEFT_ENDPOINT_LOWER_THRESHOLD: i32 = 2;
    const CASE_SHORTER_INTERVAL_LEFT_ENDPOINT_UPPER_THRESHOLD: i32 = 2 + floor_log2(
        compute_power64::<{ count_factors::<5>((1 << (SIGNIFICAND_BITS + 2)) - 1) + 1 }>(10) / 3,
    );
    exponent >= CASE_SHORTER_INTERVAL_LEFT_ENDPOINT_LOWER_THRESHOLD
        && exponent <= CASE_SHORTER_INTERVAL_LEFT_ENDPOINT_UPPER_THRESHOLD
}

const fn rotr64(n: u64, r: u32) -> u64 {
    let r = r & 63;
    (n >> r) | (n << ((64 - r) & 63))
}

fn may_have_trailing_zeros(mut significand: u64, mut exponent: i32) -> Decimal {
    // Port of the C++ remove_trailing_zeros algorithm for 64-bit
    // See https://github.com/jk-jeon/rtz_benchmark.
    // The idea of branchless search below is by reddit users r/pigeon768 and
    // r/TheoreticalDumbass.

    let mut r = rotr64(significand.wrapping_mul(28999941890838049), 8);
    let mut b = r < 184467440738;
    let mut s = b as i32;
    significand = if b { r } else { significand };

    r = rotr64(significand.wrapping_mul(182622766329724561), 4);
    b = r < 1844674407370956;
    s = s * 2 + (b as i32);
    significand = if b { r } else { significand };

    r = rotr64(significand.wrapping_mul(10330176681277348905), 2);
    b = r < 184467440737095517;
    s = s * 2 + (b as i32);
    significand = if b { r } else { significand };

    r = rotr64(significand.wrapping_mul(14757395258967641293), 1);
    b = r < 1844674407370955162;
    s = s * 2 + (b as i32);
    significand = if b { r } else { significand };

    exponent += s;

    Decimal {
        significand,
        exponent,
    }
}

#[inline(always)]
fn no_trailing_zeros(significand: u64, exponent: i32) -> Decimal {
    Decimal {
        significand,
        exponent,
    }
}

fn to_decimal(x: f64) -> Decimal {
    let br = x.to_bits();
    let exponent_bits = extract_exponent_bits(br);
    let signed_significand_bits = remove_exponent_bits(br, exponent_bits);

    let mut two_fc = remove_sign_bit_and_shift(signed_significand_bits);
    let mut exponent = exponent_bits as i32;

    // Is the input a normal number?
    if exponent != 0 {
        exponent += EXPONENT_BIAS - SIGNIFICAND_BITS as i32;

        // Shorter interval case; proceed like Schubfach. One might think this
        // condition is wrong, since when exponent_bits == 1 and two_fc == 0,
        // the interval is actually regular. However, it turns out that this
        // seemingly wrong condition is actually fine, because the end result is
        // anyway the same.
        //
        // [binary32]
        // (fc-1/2) * 2^e = 1.175'494'28... * 10^-38
        // (fc-1/4) * 2^e = 1.175'494'31... * 10^-38
        //    fc    * 2^e = 1.175'494'35... * 10^-38
        // (fc+1/2) * 2^e = 1.175'494'42... * 10^-38
        //
        // Hence, shorter_interval_case will return 1.175'494'4 * 10^-38.
        // 1.175'494'3 * 10^-38 is also a correct shortest representation that
        // will be rejected if we assume shorter interval, but 1.175'494'4 *
        // 10^-38 is closer to the true value so it doesn't matter.
        //
        // [binary64]
        // (fc-1/2) * 2^e = 2.225'073'858'507'201'13... * 10^-308
        // (fc-1/4) * 2^e = 2.225'073'858'507'201'25... * 10^-308
        //    fc    * 2^e = 2.225'073'858'507'201'38... * 10^-308
        // (fc+1/2) * 2^e = 2.225'073'858'507'201'63... * 10^-308
        //
        // Hence, shorter_interval_case will return 2.225'073'858'507'201'4 * 10^-308.
        // This is indeed of the shortest length, and it is the unique one
        // closest to the true value among valid representations of the same
        // length.
        if two_fc == 0 {
            return compute_nearest_shorter(exponent);
        }

        two_fc |= 1 << (SIGNIFICAND_BITS + 1);
    }
    // Is the input a subnormal number?
    else {
        exponent = MIN_EXPONENT - SIGNIFICAND_BITS as i32;
    }

    let even = has_even_significand_bits(signed_significand_bits);
    compute_normal_interval_case(two_fc, exponent, even, even)
}

struct MultiplyResult {
    integer_part: u64,
    is_integer: bool,
}

struct ParityResult {
    parity: bool,
    is_integer: bool,
}
