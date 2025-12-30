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

// Replace n by floor(n / 10^N).
// Returns true if and only if n is divisible by 10^N.
// Precondition: n <= 10^(N+1)
pub(crate) fn check_divisibility_and_divide_by_pow10(n: &mut u32) -> bool {
    const N: u32 = 2;
    debug_assert!(*n <= crate::compute_power32::<{ N + 1 }>(10));

    struct Info;
    impl Info {
        const MAGIC_NUMBER: u32 = 0x147c29;
        const BITS_FOR_COMPARISON: i32 = 12;
        const THRESHOLD: u32 = 0xa3;
        const SHIFT_AMOUNT: i32 = 27;
    }

    *n *= Info::MAGIC_NUMBER;

    // Mask for the lowest (N + bits_for_comparison)-bits.
    const {
        assert!(Info::BITS_FOR_COMPARISON as u32 + N < 32);
    }
    const COMPARISON_MASK: u32 = (1 << (N + Info::BITS_FOR_COMPARISON as u32)) - 1;

    // The lowest N bits of n must be zero, and (n & comparison_mask) >> N must
    // be at most threshold.
    let c = (*n & COMPARISON_MASK).rotate_right(N);

    *n >>= Info::SHIFT_AMOUNT;
    c <= Info::THRESHOLD
}
