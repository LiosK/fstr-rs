//! # FStr: stack-allocated fixed-length string type
//!
//! This crate provides a thin wrapper for `[u8; N]` to handle a stack-allocated byte array as a
//! fixed-length, [`String`]-like type through common traits such as `Display`, `PartialEq`, and
//! `Deref<Target = str>`.
//!
//! ```rust
//! use fstr::FStr;
//!
//! let x = FStr::from_inner(*b"foo")?;
//! println!("{x}"); // "foo"
//! assert_eq!(x, "foo");
//! assert_eq!(&x[..], "foo");
//! assert_eq!(&x as &str, "foo");
//! assert!(!x.is_empty());
//! assert!(x.is_ascii());
//!
//! let mut y = FStr::from_inner(*b"bar")?;
//! assert_eq!(y, "bar");
//! y.make_ascii_uppercase();
//! assert_eq!(y, "BAR");
//!
//! const K: FStr<8> = FStr::from_str_unwrap("constant");
//! assert_eq!(K, "constant");
//! # Ok::<(), std::str::Utf8Error>(())
//! ```
//!
//! Unlike [`String`], this type manages fixed-length strings only. The type parameter takes the
//! exact length (in bytes) of a concrete type, and the concrete type only holds the string values
//! of that size. Accordingly, this type is useful only when the length is considered an integral
//! part of a string type.
//!
//! ```rust
//! # use fstr::FStr;
//! let s = "Lorem Ipsum ✨";
//! assert_eq!(s.len(), 15);
//! assert!(s.parse::<FStr<15>>().is_ok()); // just right
//! assert!(s.parse::<FStr<10>>().is_err()); // too small
//! assert!(s.parse::<FStr<20>>().is_err()); // too large
//! ```
//!
//! ```compile_fail
//! # use fstr::FStr;
//! let x: FStr<10> = FStr::from_str_unwrap("helloworld");
//! let y: FStr<12> = FStr::from_str_unwrap("helloworld  ");
//!
//! // This code does not compile because `FStr` of different lengths cannot mix.
//! if x != y {
//!     unreachable!();
//! }
//! ```
//!
//! ## Crate features
//!
//! - `std` (optional; enabled by default) enables the integration with [`std`]. Disable default
//!   features to operate this crate under `no_std` environments.
//! - `serde` (optional) enables the serialization and deserialization of `FStr`through [`serde`].

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(not(feature = "std"))]
use core as std;
use std::{borrow, fmt, hash, ops, str};

/// Stack-allocated fixed-length string type.
///
/// See [the crate-level documentation](crate) for details.
#[derive(Copy, Clone, Eq, Ord, PartialOrd, Debug)]
pub struct FStr<const N: usize> {
    inner: [u8; N],
}

impl<const N: usize> FStr<N> {
    /// Returns a string slice of the content.
    #[inline]
    pub const fn as_str(&self) -> &str {
        debug_assert!(str::from_utf8(&self.inner).is_ok());
        // SAFETY: constructors must guarantee that `inner` is a valid UTF-8 sequence.
        unsafe { str::from_utf8_unchecked(&self.inner) }
    }

    /// Returns a mutable string slice of the content.
    fn as_mut_str(&mut self) -> &mut str {
        debug_assert!(str::from_utf8(&self.inner).is_ok());
        // SAFETY: constructors must guarantee that `inner` is a valid UTF-8 sequence.
        unsafe { str::from_utf8_unchecked_mut(&mut self.inner) }
    }

    /// Returns a reference to the underlying byte array.
    #[inline]
    pub const fn as_bytes(&self) -> &[u8; N] {
        &self.inner
    }

    /// Extracts the underlying byte array.
    #[inline]
    pub const fn into_inner(self) -> [u8; N] {
        self.inner
    }

    /// Creates a value from a fixed-length byte array.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the bytes passed in are not valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fstr::FStr;
    /// let x = FStr::from_inner(*b"foo")?;
    /// assert_eq!(x, "foo");
    /// # Ok::<(), std::str::Utf8Error>(())
    /// ```
    #[inline]
    pub const fn from_inner(utf8_bytes: [u8; N]) -> Result<Self, str::Utf8Error> {
        match str::from_utf8(&utf8_bytes) {
            Ok(_) => Ok(Self { inner: utf8_bytes }),
            Err(e) => Err(e),
        }
    }

    /// Creates a value from a byte array without checking that the bytes are valid UTF-8.
    ///
    /// # Safety
    ///
    /// The byte array passed in must contain a valid UTF-8 byte sequence.
    #[inline]
    pub const unsafe fn from_inner_unchecked(utf8_bytes: [u8; N]) -> Self {
        debug_assert!(str::from_utf8(&utf8_bytes).is_ok());
        Self { inner: utf8_bytes }
    }

    /// A `const`-friendly equivalent of `Self::from_str(s).unwrap()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fstr::FStr;
    /// use std::str::FromStr;
    ///
    /// const K: FStr<3> = FStr::from_str_unwrap("foo");
    /// assert_eq!(K, FStr::from_str("foo").unwrap());
    /// ```
    #[inline]
    pub const fn from_str_unwrap(s: &str) -> Self {
        match Self::from_str_const(s) {
            Ok(t) => t,
            _ => panic!("invalid byte length"),
        }
    }

    /// Creates a value from a string slice in the `const` context.
    const fn from_str_const(s: &str) -> Result<Self, LengthError> {
        let s = s.as_bytes();
        if s.len() == N {
            let ptr = s.as_ptr() as *const [u8; N];
            // SAFETY: ok because `s.len() == N`
            let utf8_bytes = unsafe { *ptr };
            // SAFETY: ok because `utf8_bytes` came from `&str`
            Ok(unsafe { Self::from_inner_unchecked(utf8_bytes) })
        } else {
            Err(LengthError {
                actual: s.len(),
                expected: N,
            })
        }
    }
}

impl<const N: usize> ops::Deref for FStr<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for FStr<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> Default for FStr<N> {
    /// Returns a fixed-length string value filled by white spaces (`U+0020`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fstr::FStr;
    /// assert_eq!(FStr::<4>::default(), "    ");
    /// assert_eq!(FStr::<8>::default(), "        ");
    /// ```
    #[inline]
    fn default() -> Self {
        unsafe { Self::from_inner_unchecked([b' '; N]) }
    }
}

impl<const N: usize> fmt::Display for FStr<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl<const N: usize> PartialEq for FStr<N> {
    #[inline]
    fn eq(&self, other: &FStr<N>) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl<const N: usize> PartialEq<str> for FStr<N> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

impl<const N: usize> PartialEq<FStr<N>> for str {
    #[inline]
    fn eq(&self, other: &FStr<N>) -> bool {
        other.eq(self)
    }
}

impl<const N: usize> PartialEq<&str> for FStr<N> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.as_str().eq(*other)
    }
}

impl<const N: usize> PartialEq<FStr<N>> for &str {
    #[inline]
    fn eq(&self, other: &FStr<N>) -> bool {
        other.eq(self)
    }
}

impl<const N: usize> hash::Hash for FStr<N> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        self.as_str().hash(hasher)
    }
}

impl<const N: usize> borrow::Borrow<str> for FStr<N> {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> borrow::BorrowMut<str> for FStr<N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> AsRef<str> for FStr<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsMut<str> for FStr<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> AsRef<[u8]> for FStr<N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> From<FStr<N>> for [u8; N] {
    #[inline]
    fn from(value: FStr<N>) -> Self {
        value.into_inner()
    }
}

impl<const N: usize> str::FromStr for FStr<N> {
    type Err = LengthError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str_const(s)
    }
}

/// Error converting to [`FStr<N>`] from a byte slice having a different length than `N`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct LengthError {
    actual: usize,
    expected: usize,
}

impl fmt::Display for LengthError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid byte length of {} (expected: {})",
            self.actual, self.expected
        )
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_integration {
    use super::{FStr, LengthError};

    impl<const N: usize> From<FStr<N>> for String {
        fn from(value: FStr<N>) -> Self {
            value.as_str().to_owned()
        }
    }

    impl<const N: usize> TryFrom<String> for FStr<N> {
        type Error = LengthError;

        fn try_from(value: String) -> Result<Self, Self::Error> {
            value.parse()
        }
    }

    impl<const N: usize> PartialEq<String> for FStr<N> {
        fn eq(&self, other: &String) -> bool {
            self.as_str().eq(other.as_str())
        }
    }

    impl<const N: usize> PartialEq<FStr<N>> for String {
        fn eq(&self, other: &FStr<N>) -> bool {
            other.eq(self)
        }
    }

    impl std::error::Error for LengthError {}
}

#[cfg(test)]
mod tests {
    use super::FStr;

    /// Tests `PartialEq` implementations.
    #[test]
    fn eq() {
        let x = FStr::from_inner(*b"hello").unwrap();

        assert_eq!(x, x);
        assert_eq!(&x, &x);
        assert_eq!(x, FStr::from_inner(*b"hello").unwrap());
        assert_eq!(FStr::from_inner(*b"hello").unwrap(), x);
        assert_eq!(&x, &FStr::from_inner(*b"hello").unwrap());
        assert_eq!(&FStr::from_inner(*b"hello").unwrap(), &x);

        assert_eq!(x, "hello");
        assert_eq!("hello", x);
        assert_eq!(&x, "hello");
        assert_eq!("hello", &x);
        assert_eq!(&x[..], "hello");
        assert_eq!("hello", &x[..]);
        assert_eq!(&x as &str, "hello");
        assert_eq!("hello", &x as &str);

        assert_ne!(x, FStr::from_inner(*b"world").unwrap());
        assert_ne!(FStr::from_inner(*b"world").unwrap(), x);
        assert_ne!(&x, &FStr::from_inner(*b"world").unwrap());
        assert_ne!(&FStr::from_inner(*b"world").unwrap(), &x);

        assert_ne!(x, "world");
        assert_ne!("world", x);
        assert_ne!(&x, "world");
        assert_ne!("world", &x);
        assert_ne!(&x[..], "world");
        assert_ne!("world", &x[..]);
        assert_ne!(&x as &str, "world");
        assert_ne!("world", &x as &str);

        #[cfg(feature = "std")]
        {
            assert_eq!(x, String::from("hello"));
            assert_eq!(String::from("hello"), x);

            assert_eq!(String::from(x), String::from("hello"));
            assert_eq!(String::from("hello"), String::from(x));

            assert_ne!(x, String::from("world"));
            assert_ne!(String::from("world"), x);

            assert_ne!(String::from(x), String::from("world"));
            assert_ne!(String::from("world"), String::from(x));

            assert_eq!(x.to_owned(), String::from("hello"));
            assert_eq!(String::from("hello"), x.to_owned());
            assert_eq!(x.to_string(), String::from("hello"));
            assert_eq!(String::from("hello"), x.to_string());
        }
    }

    /// Tests `FromStr` implementation.
    #[test]
    fn from_str() {
        assert!("ceremony".parse::<FStr<4>>().is_err());
        assert!("strategy".parse::<FStr<12>>().is_err());
        assert!("parallel".parse::<FStr<8>>().is_ok());
        assert_eq!("parallel".parse::<FStr<8>>().unwrap(), "parallel");

        assert!("😂".parse::<FStr<2>>().is_err());
        assert!("😂".parse::<FStr<6>>().is_err());
        assert!("😂".parse::<FStr<4>>().is_ok());
        assert_eq!("😂".parse::<FStr<4>>().unwrap(), "😂");
    }

    /// Tests `Hash` and `Borrow` implementations using `HashSet`.
    #[cfg(feature = "std")]
    #[test]
    fn hash_borrow() {
        use std::collections::HashSet;

        let mut s = HashSet::new();
        s.insert(FStr::from_inner(*b"crisis").unwrap());
        s.insert(FStr::from_inner(*b"eating").unwrap());
        s.insert(FStr::from_inner(*b"lucent").unwrap());

        assert!(s.contains("crisis"));
        assert!(s.contains("eating"));
        assert!(s.contains("lucent"));
        assert!(!s.contains("system"));
        assert!(!s.contains("unless"));
        assert!(!s.contains("yellow"));

        assert!(s.contains(&FStr::from_inner(*b"crisis").unwrap()));
        assert!(s.contains(&FStr::from_inner(*b"eating").unwrap()));
        assert!(s.contains(&FStr::from_inner(*b"lucent").unwrap()));
        assert!(!s.contains(&FStr::from_inner(*b"system").unwrap()));
        assert!(!s.contains(&FStr::from_inner(*b"unless").unwrap()));
        assert!(!s.contains(&FStr::from_inner(*b"yellow").unwrap()));
    }
}

#[cfg(feature = "serde")]
mod serde_integration {
    use super::{fmt, FStr};
    use serde::{de, Deserializer, Serializer};

    impl<const N: usize> serde::Serialize for FStr<N> {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_str(self.as_str())
        }
    }

    impl<'de, const N: usize> serde::Deserialize<'de> for FStr<N> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_str(VisitorImpl)
        }
    }

    struct VisitorImpl<const N: usize>;

    impl<'de, const N: usize> de::Visitor<'de> for VisitorImpl<N> {
        type Value = FStr<N>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "a fixed-length string")
        }

        fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
            value.parse().map_err(de::Error::custom)
        }
    }

    #[test]
    fn ser_de() {
        use serde_test::Token;

        let x = FStr::from_inner(*b"helloworld").unwrap();
        serde_test::assert_tokens(&x, &[Token::Str("helloworld")]);
    }
}
