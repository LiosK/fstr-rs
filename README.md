# FStr: stack-allocated fixed-length string type

[![Crates.io](https://img.shields.io/crates/v/fstr)](https://crates.io/crates/fstr)
[![License](https://img.shields.io/crates/l/fstr)](https://github.com/LiosK/fstr-rs/blob/main/LICENSE)

This crate provides a thin wrapper for `[u8; N]` to handle a stack-allocated byte array as a
fixed-length, `String`-like type through common traits such as `Display`, `PartialEq`, and
`Deref<Target = str>`.

```rust
use fstr::FStr;

let x = FStr::from_inner(*b"foo")?;
println!("{x}"); // "foo"
assert_eq!(x, "foo");
assert_eq!(&x[..], "foo");
assert_eq!(&x as &str, "foo");
assert!(!x.is_empty());
assert!(x.is_ascii());

let mut y = FStr::from_inner(*b"bar")?;
assert_eq!(y, "bar");
y.make_ascii_uppercase();
assert_eq!(y, "BAR");

const K: FStr<8> = FStr::from_str_unwrap("constant");
assert_eq!(K, "constant");
```

Unlike `String`, this type manages fixed-length strings only. The type parameter takes the
exact length (in bytes) of a concrete type, and the concrete type only holds the string values
of that size. Accordingly, this type is useful only when the length is considered an integral
part of a string type.

```rust
let s = "Lorem Ipsum ✨";
assert_eq!(s.len(), 15);
assert!(s.parse::<FStr<15>>().is_ok()); // just right
assert!(s.parse::<FStr<10>>().is_err()); // too small
assert!(s.parse::<FStr<20>>().is_err()); // too large
```

```rust
let x: FStr<10> = FStr::from_str_unwrap("helloworld");
let y: FStr<12> = FStr::from_str_unwrap("helloworld  ");

// This code does not compile because `FStr` of different lengths cannot mix.
if x != y {
    unreachable!();
}
```

## Crate features

- `std` (optional; enabled by default) enables the integration with `std`. Disable default
  features to operate this crate under `no_std` environments.
- `serde` (optional) enables the serialization and deserialization of `FStr`through `serde`.

## License

Licensed under the Apache License, Version 2.0.

## See also

- [docs.rs/fstr](https://docs.rs/fstr)
