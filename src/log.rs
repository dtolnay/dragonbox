// Translated from C++ to Rust. The original C++ code can be found at
// https://github.com/jk-jeon/dragonbox and carries the following license:
//
// Copyright 2020-2024 Junekey Jeon
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

////////////////////////////////////////////////////////////////////////////////////////
// Utilities for fast/constexpr log computation.
////////////////////////////////////////////////////////////////////////////////////////

const _: () = assert!(
    (-1 >> 1) == -1,
    "right-shift for signed integers must be arithmetic",
);

// Compute floor((e * m - f) >> k) for given e.
type Multiply = u32;
type Subtract = u32;
type Shift = usize;
type MinExponent = i32;
type MaxExponent = i32;

const fn compute<
    const M: Multiply,
    const F: Subtract,
    const K: Shift,
    const E_MIN: MinExponent,
    const E_MAX: MaxExponent,
>(
    e: i32,
) -> i32 {
    debug_assert!(E_MIN <= e && e <= E_MAX);
    (e * M as i32 - F as i32) >> K
}

const FLOOR_LOG10_POW2_MIN_EXPONENT: i32 = -2620;
const FLOOR_LOG10_POW2_MAX_EXPONENT: i32 = 2620;
pub(crate) const fn floor_log10_pow2(e: i32) -> i32 {
    compute::<315653, 0, 20, FLOOR_LOG10_POW2_MIN_EXPONENT, FLOOR_LOG10_POW2_MAX_EXPONENT>(e)
}

const FLOOR_LOG2_POW10_MIN_EXPONENT: i32 = -1233;
const FLOOR_LOG2_POW10_MAX_EXPONENT: i32 = 1233;
pub(crate) const fn floor_log2_pow10(e: i32) -> i32 {
    compute::<1741647, 0, 19, FLOOR_LOG2_POW10_MIN_EXPONENT, FLOOR_LOG2_POW10_MAX_EXPONENT>(e)
}

const FLOOR_LOG10_POW2_MINUS_LOG10_4_OVER_3_MIN_EXPONENT: i32 = -2985;
const FLOOR_LOG10_POW2_MINUS_LOG10_4_OVER_3_MAX_EXPONENT: i32 = 2936;
pub(crate) const fn floor_log10_pow2_minus_log10_4_over_3(e: i32) -> i32 {
    compute::<
        631305,
        261663,
        21,
        FLOOR_LOG10_POW2_MINUS_LOG10_4_OVER_3_MIN_EXPONENT,
        FLOOR_LOG10_POW2_MINUS_LOG10_4_OVER_3_MAX_EXPONENT,
    >(e)
}

const FLOOR_LOG5_POW2_MIN_EXPONENT: i32 = -1831;
const FLOOR_LOG5_POW2_MAX_EXPONENT: i32 = 1831;
pub(crate) const fn floor_log5_pow2(e: i32) -> i32 {
    compute::<225799, 0, 19, FLOOR_LOG5_POW2_MIN_EXPONENT, FLOOR_LOG5_POW2_MAX_EXPONENT>(e)
}

const FLOOR_LOG5_POW2_MINUS_LOG5_3_MIN_EXPONENT: i32 = -3543;
const FLOOR_LOG5_POW2_MINUS_LOG5_3_MAX_EXPONENT: i32 = 2427;
pub(crate) const fn floor_log5_pow2_minus_log5_3(e: i32) -> i32 {
    compute::<
        451597,
        715764,
        20,
        FLOOR_LOG5_POW2_MINUS_LOG5_3_MIN_EXPONENT,
        FLOOR_LOG5_POW2_MINUS_LOG5_3_MAX_EXPONENT,
    >(e)
}
