# Dragonbox

[<img alt="github" src="https://img.shields.io/badge/github-dtolnay/dragonbox-8da0cb?style=for-the-badge&labelColor=555555&logo=github" height="20">](https://github.com/dtolnay/dragonbox)
[<img alt="crates.io" src="https://img.shields.io/crates/v/dragonbox.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/dragonbox)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-dragonbox-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/dragonbox)
[<img alt="build status" src="https://img.shields.io/github/workflow/status/dtolnay/dragonbox/CI/master?style=for-the-badge" height="20">](https://github.com/dtolnay/dragonbox/actions?query=branch%3Amaster)

This crate contains a basic port of <https://github.com/jk-jeon/dragonbox> to
Rust for benchmarking purposes.

Please see the upstream repo for an explanation of the approach and comparison
to the Ryū algorithm.

<br>

## Example

```rust
fn main() {
    let mut buffer = dragonbox::Buffer::new();
    let printed = buffer.format(1.234);
    assert_eq!(printed, "1.234E0");
}
```

<br>

## Performance (lower is better)

![performance](https://raw.githubusercontent.com/dtolnay/dragonbox/master/performance.png)

<br>

#### License

<sup>
Licensed under either of <a href="LICENSE-Apache2-LLVM">Apache License, Version
2.0 with LLVM Exceptions</a> or <a href="LICENSE-Boost">Boost Software License
Version 1.0</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
