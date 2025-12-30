// Translated from C++ to Rust. The original C++ code can be found at
// https://github.com/jk-jeon/dragonbox and carries the following license:
//
// Copyright 2020-2022 Junekey Jeon
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

use crate::{log, wuint};

// Replace n by floor(n / 10^N).
// Returns true if and only if n is divisible by 10^N.
// Precondition: n <= 10^(N+1)
pub(crate) fn check_divisibility_and_divide_by_pow10(n: &mut u32) -> bool {
    const N: u32 = 2;
    debug_assert!(*n <= crate::compute_power32::<{ N + 1 }>(10));

    struct Info;
    impl Info {
        const MAGIC_NUMBER: u32 = 656;
        const DIVISIBILITY_CHECK_BITS: i32 = 16;
    }

    *n *= Info::MAGIC_NUMBER;

    const {
        assert!(Info::DIVISIBILITY_CHECK_BITS < 32);
    }
    const MASK: u32 = (1 << Info::DIVISIBILITY_CHECK_BITS) - 1;
    let result = (*n & MASK) < Info::MAGIC_NUMBER;

    *n >>= Info::DIVISIBILITY_CHECK_BITS;
    result
}

// Compute floor(n / 10^N) for small N.
// Precondition: n <= 2^a * 5^b (a = max_pow2, b = max_pow5)
pub(crate) fn divide_by_pow10<const N: u32, const MAX_POW2: i32, const MAX_POW5: i32>(
    n: u64,
) -> u64 {
    // Ensure no overflow.
    assert!(MAX_POW2 + (log::floor_log2_pow10(MAX_POW5) - MAX_POW5) < 64);

    // Specialize for 64-bit division by 1000.
    // Ensure that the correctness condition is met.
    if N == 3
        && MAX_POW2 + (log::floor_log2_pow10(N as i32 + MAX_POW5) - (N as i32 + MAX_POW5)) < 70
    {
        wuint::umul128_upper64(n, 0x8312_6e97_8d4f_df3c) >> 9
    } else {
        let divisor = const { crate::compute_power64::<N>(10) };
        n / divisor
    }
}
