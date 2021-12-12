#![feature(test)]

extern crate test;

use std::io::Write;
use test::{black_box, Bencher};

macro_rules! benches {
    ($($name:ident($value:expr),)*) => {
        mod bench_dragonbox {
            use super::*;
            $(
                #[bench]
                fn $name(b: &mut Bencher) {
                    let mut buf = dragonbox::Buffer::new();

                    b.iter(move || {
                        let value = black_box($value);
                        let formatted = buf.format_finite(value);
                        black_box(formatted);
                    });
                }
            )*
        }

        mod bench_std_fmt {
            use super::*;
            $(
                #[bench]
                fn $name(b: &mut Bencher) {
                    let mut buf = Vec::with_capacity(20);

                    b.iter(|| {
                        buf.clear();
                        let value = black_box($value);
                        write!(&mut buf, "{}", value).unwrap();
                        black_box(buf.as_slice());
                    });
                }
            )*
        }
    };
}

benches! {
    bench_0_f64(0f64),
    bench_short_f64(0.1234f64),
    bench_e_f64(2.718281828459045f64),
    bench_max_f64(f64::MAX),
}
