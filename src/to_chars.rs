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

use core::ptr;

// sign(1) + significand(17) + decimal_point(1) + exp_marker(1) + exp_sign(1) + exp(3)
pub(crate) const MAX_OUTPUT_STRING_LENGTH: usize = 1 + 17 + 1 + 1 + 1 + 3;

pub(crate) unsafe fn to_chars(x: f64, mut buffer: *mut u8) -> *mut u8 {
    let br = x.to_bits();
    let exponent_bits = crate::extract_exponent_bits(br);
    let s = crate::remove_exponent_bits(br, exponent_bits);

    if crate::is_negative(s) {
        *buffer = b'-';
        buffer = buffer.add(1);
    }

    if crate::is_nonzero(br) {
        let result = crate::to_decimal(x);
        to_chars_detail(result.significand, result.exponent, buffer)
    } else {
        ptr::copy_nonoverlapping(b"0E0".as_ptr(), buffer, 3);
        buffer.add(3)
    }
}

static RADIX_100_TABLE: [u8; 200] = [
    b'0', b'0', b'0', b'1', b'0', b'2', b'0', b'3', b'0', b'4', //
    b'0', b'5', b'0', b'6', b'0', b'7', b'0', b'8', b'0', b'9', //
    b'1', b'0', b'1', b'1', b'1', b'2', b'1', b'3', b'1', b'4', //
    b'1', b'5', b'1', b'6', b'1', b'7', b'1', b'8', b'1', b'9', //
    b'2', b'0', b'2', b'1', b'2', b'2', b'2', b'3', b'2', b'4', //
    b'2', b'5', b'2', b'6', b'2', b'7', b'2', b'8', b'2', b'9', //
    b'3', b'0', b'3', b'1', b'3', b'2', b'3', b'3', b'3', b'4', //
    b'3', b'5', b'3', b'6', b'3', b'7', b'3', b'8', b'3', b'9', //
    b'4', b'0', b'4', b'1', b'4', b'2', b'4', b'3', b'4', b'4', //
    b'4', b'5', b'4', b'6', b'4', b'7', b'4', b'8', b'4', b'9', //
    b'5', b'0', b'5', b'1', b'5', b'2', b'5', b'3', b'5', b'4', //
    b'5', b'5', b'5', b'6', b'5', b'7', b'5', b'8', b'5', b'9', //
    b'6', b'0', b'6', b'1', b'6', b'2', b'6', b'3', b'6', b'4', //
    b'6', b'5', b'6', b'6', b'6', b'7', b'6', b'8', b'6', b'9', //
    b'7', b'0', b'7', b'1', b'7', b'2', b'7', b'3', b'7', b'4', //
    b'7', b'5', b'7', b'6', b'7', b'7', b'7', b'8', b'7', b'9', //
    b'8', b'0', b'8', b'1', b'8', b'2', b'8', b'3', b'8', b'4', //
    b'8', b'5', b'8', b'6', b'8', b'7', b'8', b'8', b'8', b'9', //
    b'9', b'0', b'9', b'1', b'9', b'2', b'9', b'3', b'9', b'4', //
    b'9', b'5', b'9', b'6', b'9', b'7', b'9', b'8', b'9', b'9', //
];

// These digit generation routines are inspired by James Anhalt's itoa
// algorithm: https://github.com/jeaiii/itoa
// The main idea is for given n, find y such that floor(10^k * y / 2^32) = n
// holds, where k is an appropriate integer depending on the length of n. For
// example, if n = 1234567, we set k = 6. In this case, we have
// floor(y / 2^32) = 1,
// floor(10^2 * (y mod 2^32) / 2^32) = 23,
// floor(10^2 * (10^2 * y mod 2^32) / 2^32) = 45, and
// floor(10^2 * (10^4 * y mod 2^32) / 2^32) = 67.

unsafe fn to_chars_detail(significand: u64, mut exponent: i32, mut buffer: *mut u8) -> *mut u8 {
    let first_block: u32;
    let second_block: u32;
    let have_second_block: bool;

    if significand < 1_0000_0000 {
        first_block = significand as u32;
        second_block = 0;
        have_second_block = false;
    } else {
        first_block = (significand / 1_0000_0000) as u32;
        second_block = (significand as u32).wrapping_sub(first_block.wrapping_mul(1_0000_0000));
        have_second_block = true;
    }

    // Print significand.
    if first_block < 100 {
        if first_block < 10 {
            // 1 digit.
            *buffer = b'0' + first_block as u8;
            if have_second_block {
                *buffer.add(1) = b'.';
                buffer = buffer.add(2);
            } else {
                buffer = buffer.add(1);
            }
        } else {
            // 2 digits.
            *buffer = *RADIX_100_TABLE.get_unchecked((first_block * 2) as usize);
            *buffer.add(1) = b'.';
            *buffer.add(2) = *RADIX_100_TABLE.get_unchecked((first_block * 2 + 1) as usize);
            buffer = buffer.add(3);
            exponent += 1;
        }
    } else if first_block < 100_0000 {
        if first_block < 1_0000 {
            // 42949673 = ceil(2^32 / 100)
            let mut prod = u64::from(first_block) * 42949673;
            let first_two_digits = (prod >> 32) as u32;

            prod = u64::from(prod as u32) * 100;
            let second_two_digits = (prod >> 32) as u32;

            if first_two_digits < 10 {
                // 3 digits.
                *buffer = b'0' + first_two_digits as u8;
                *buffer.add(1) = b'.';
                buffer = buffer.add(2);
                exponent += 2;
            } else {
                // 4 digits.
                *buffer = *RADIX_100_TABLE.get_unchecked((first_two_digits * 2) as usize);
                *buffer.add(1) = b'.';
                *buffer.add(2) =
                    *RADIX_100_TABLE.get_unchecked((first_two_digits * 2 + 1) as usize);
                buffer = buffer.add(3);
                exponent += 3;
            }

            ptr::copy_nonoverlapping(
                RADIX_100_TABLE
                    .as_ptr()
                    .add((second_two_digits * 2) as usize),
                buffer,
                2,
            );
            buffer = buffer.add(2);
        } else {
            // 429497 = ceil(2^32 / 1_0000)
            let mut prod = u64::from(first_block) * 429497;
            let first_two_digits = (prod >> 32) as u32;

            prod = u64::from(prod as u32) * 100;
            let second_two_digits = (prod >> 32) as u32;

            prod = u64::from(prod as u32) * 100;
            let third_two_digits = (prod >> 32) as u32;

            if first_two_digits < 10 {
                // 5 digits.
                *buffer = b'0' + first_two_digits as u8;
                *buffer.add(1) = b'.';
                buffer = buffer.add(2);
                exponent += 4;
            } else {
                // 6 digits.
                *buffer = *RADIX_100_TABLE.get_unchecked((first_two_digits * 2) as usize);
                *buffer.add(1) = b'.';
                *buffer.add(2) =
                    *RADIX_100_TABLE.get_unchecked((first_two_digits * 2 + 1) as usize);
                buffer = buffer.add(3);
                exponent += 5;
            }

            ptr::copy_nonoverlapping(
                RADIX_100_TABLE
                    .as_ptr()
                    .add((second_two_digits * 2) as usize),
                buffer,
                2,
            );
            ptr::copy_nonoverlapping(
                RADIX_100_TABLE
                    .as_ptr()
                    .add((third_two_digits * 2) as usize),
                buffer.add(2),
                2,
            );
            buffer = buffer.add(4);
        }
    } else if first_block < 1_0000_0000 {
        // 281474978 = ceil(2^48 / 100_0000) + 1
        let mut prod = u64::from(first_block) * 281474978;
        prod >>= 16;
        let first_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let second_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let third_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let fourth_two_digits = (prod >> 32) as u32;

        if first_two_digits < 10 {
            // 7 digits.
            *buffer = b'0' + first_two_digits as u8;
            *buffer.add(1) = b'.';
            buffer = buffer.add(2);
            exponent += 6;
        } else {
            // 8 digits.
            *buffer = *RADIX_100_TABLE.get_unchecked((first_two_digits * 2) as usize);
            *buffer.add(1) = b'.';
            *buffer.add(2) = *RADIX_100_TABLE.get_unchecked((first_two_digits * 2 + 1) as usize);
            buffer = buffer.add(3);
            exponent += 7;
        }

        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((second_two_digits * 2) as usize),
            buffer,
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((third_two_digits * 2) as usize),
            buffer.add(2),
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((fourth_two_digits * 2) as usize),
            buffer.add(4),
            2,
        );
        buffer = buffer.add(6);
    } else {
        // 9 digits.
        // 2882303763 = ceil(2^58 / 1_0000_0000) + 1
        let mut prod = u64::from(first_block) * 2882303763;
        prod >>= 26;
        let first_digit = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let second_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let third_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let fourth_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let fifth_two_digits = (prod >> 32) as u32;

        *buffer = b'0' + first_digit as u8;
        *buffer.add(1) = b'.';
        buffer = buffer.add(2);
        exponent += 8;

        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((second_two_digits * 2) as usize),
            buffer,
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((third_two_digits * 2) as usize),
            buffer.add(2),
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((fourth_two_digits * 2) as usize),
            buffer.add(4),
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((fifth_two_digits * 2) as usize),
            buffer.add(6),
            2,
        );
        buffer = buffer.add(8);
    }

    // Print second block if necessary.
    if have_second_block {
        // 281474978 = ceil(2^48 / 100_0000) + 1
        let mut prod = u64::from(second_block) * 281474978;
        prod >>= 16;
        prod += 1;
        let first_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let second_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let third_two_digits = (prod >> 32) as u32;

        prod = u64::from(prod as u32) * 100;
        let fourth_two_digits = (prod >> 32) as u32;

        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((first_two_digits * 2) as usize),
            buffer,
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((second_two_digits * 2) as usize),
            buffer.add(2),
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((third_two_digits * 2) as usize),
            buffer.add(4),
            2,
        );
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE
                .as_ptr()
                .add((fourth_two_digits * 2) as usize),
            buffer.add(6),
            2,
        );
        buffer = buffer.add(8);

        exponent += 8;
    }

    // Print exponent and return
    if exponent < 0 {
        ptr::copy_nonoverlapping(b"E-".as_ptr(), buffer, 2);
        buffer = buffer.add(2);
        exponent = -exponent;
    } else {
        *buffer = b'E';
        buffer = buffer.add(1);
    }

    if exponent >= 100 {
        // d1 = exponent / 10; d2 = exponent % 10;
        // 6554 = ceil(2^16 / 10)
        let mut prod = exponent as u32 * 6554;
        let d1 = prod >> 16;
        prod = u32::from(prod as u16) * 10;
        let d2 = prod >> 16;
        ptr::copy_nonoverlapping(RADIX_100_TABLE.as_ptr().add((d1 * 2) as usize), buffer, 2);
        *buffer.add(2) = b'0' + d2 as u8;
        buffer = buffer.add(3);
    } else if exponent >= 10 {
        ptr::copy_nonoverlapping(
            RADIX_100_TABLE.as_ptr().add((exponent * 2) as usize),
            buffer,
            2,
        );
        buffer = buffer.add(2);
    } else {
        *buffer = b'0' + exponent as u8;
        buffer = buffer.add(1);
    }

    buffer
}
