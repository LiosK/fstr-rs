# Changelog

## Unreleased

- Added CHANGELOG.md to the repository.

## v0.2.20 - 2026-05-17

### New features

- Added `fstr!` convenience macro for easier creation of `FStr` values with
  formatted content.
- Implemented `TryFrom<&str>` for `FStr` to improve ergonomics when converting
  from string literals.

### Renamings

- The following constant and methods of `FStr` are renamed for better
  readability and consistency. Old names are kept as deprecated synonyms for
  backward compatibility:
  - `LENGTH` -> `LEN`
  - `into_inner()` -> `into_bytes()`
  - `from_inner()` -> `from_bytes()`
  - `from_inner_unchecked()` -> `from_bytes_unchecked()`
  - `from_str_unwrap()` -> `from_str_const()`
  - `slice_to_terminator()` -> `slice_up_to()`

### Other

- Refactored tests requiring `std` into the `tests/` directory.
- Other minor refactoring and documentation adjustments.

## v0.2.19 - 2026-05-07

- Added `#[track_caller]` to improve panic diagnosis.
- Minor refactoring.

## v0.2.18 - 2026-04-24

- Added `actual()` and `expected()` to `LengthError`.
- Other minor refactoring.

## v0.2.17 - 2026-02-21

- Migrated to Edition 2024 and upgraded MSRV to 1.85.
- Marked `FStr::as_mut_str()` as const.
- Implemented `core::error::Error` for `LengthError` and `FromSliceError` in
  `no_std` environments.
- Other minor refactoring.

## v0.2.16 - 2026-02-21

- Minor refactoring.

## v0.2.15 - 2025-10-15

- Added `alloc` crate feature and moved the integration with `String` from
  `std`.
- Added `FStr::as_mut_str()`.
- Other minor refactoring.

## v0.2.14 - 2025-10-03

- Added `rust-version = "1.63"` key to Cargo.toml.

## v0.2.13 - 2025-02-23

- Deprecated `FStr::writer` to simplify API; use `writer_at(0)`.
- Updated Cargo.lock.
- Updated documents.

## v0.2.12 - 2024-10-13

- Added `FStr::from_fmt()`.
- Published `Cursor`, the return type of `FStr::writer()`.
- Renamed `FStr::repeat()` to `FStr::from_ascii_filler()`, leaving the old name
  as a deprecated alias to maintain backward compatibility.
- Made minor refactoring and code reorganization.

## v0.2.11 - 2024-08-17

- Minor refactoring.

## v0.2.10 - 2023-11-20

- Fixed #1 Soundness issue: writing to an `as_ptr` pointer is UB.

## v0.2.9 - 2023-10-03

- Minor refactoring and test case improvements.

## v0.2.8 - 2023-10-02

- Exposed `Debug` implementation of struct returned by `writer()`.
- Refactored `from_str_lossy()` to lower minimum compatible Rust version.

## v0.2.7 - 2023-09-16

- Removed redundant #[inline] attributes.

## v0.2.6 - 2023-09-16

### Added

- `TryFrom<&[u8]>` implementation.
- `FromSliceError`.

### Maintenance

- Other refactoring and internal improvements.

## v0.2.5 - 2023-09-11

- Removed `Hash` and `Default` implementations from `LengthError` as they might
  cause nonsensical consequences.

## v0.2.4 - 2023-07-10

- Changed `fmt::Debug` implementation to present the length of inner array.

## v0.2.3 - 2023-06-11

- Added `impl TryFrom<[u8; N]>` and `impl TryFrom<&[u8; N]>` that allow
  `FStr::try_from(b"foo")?` syntax.

## v0.2.2 - 2023-04-06

- Refactored internal structure.

## v0.2.1 - 2023-04-05

- Refactored internal structure.

## v0.2.0 - 2023-04-01

### Changed

- `fmt::Display` implementation; it now supports width, fill/align, and
  precision flags (e.g., `{:5}`, `{:^7.3}`), which used to be ignored.
- `fmt::Debug` representation.

### Added

- `repeat`.
- Deserialization support from byte slice.

## v0.1.6 - 2023-03-30

- Added `writer_at()`.

## v0.1.5 - 2023-03-28

- Added `writer()` to support `fmt::Write` operations.

## v0.1.4 - 2022-12-21

- Added `LENGTH` type constant.
- Added `#[repr(transparent)]` guarantee.

## v0.1.3 - 2022-12-09

- Added `from_str_lossy()` and `slice_to_terminator()`.

## v0.1.2 - 2022-12-06

- Added #[inline] attribute to some functions.

## v0.1.1 - 2022-11-23

- v0.1.1 Released
