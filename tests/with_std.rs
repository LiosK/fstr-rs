use fstr::FStr;

/// Tests `PartialOrd` implementations.
#[test]
fn test_ord_partial_ord() {
    use std::collections::BTreeSet;

    let mut set = BTreeSet::new();
    set.insert(FStr::try_from(b"apple").unwrap());
    set.insert(FStr::try_from(b"zebra").unwrap());
    set.insert(FStr::try_from(b"apple").unwrap());
    set.insert(FStr::try_from(b"berry").unwrap());

    let vec: Vec<_> = set.into_iter().collect();
    assert_eq!(vec.len(), 3);
    assert_eq!(vec[0], "apple");
    assert_eq!(vec[1], "berry");
    assert_eq!(vec[2], "zebra");

    let a = FStr::try_from(b"apple").unwrap();
    let b = FStr::try_from(b"berry").unwrap();
    assert!(a < b);
    assert!(a <= b);
    assert!(b > a);
    assert!(b >= a);
    assert!(a <= a);
    assert!(a >= a);
}

/// Tests `Hash` and `Borrow` implementations using `HashSet`.
#[test]
fn hash_borrow() {
    use std::collections::HashSet;

    let mut s = HashSet::new();
    s.insert(FStr::from_bytes(*b"crisis").unwrap());
    s.insert(FStr::from_bytes(*b"eating").unwrap());
    s.insert(FStr::from_bytes(*b"lucent").unwrap());

    assert!(s.contains("crisis"));
    assert!(s.contains("eating"));
    assert!(s.contains("lucent"));
    assert!(!s.contains("system"));
    assert!(!s.contains("unless"));
    assert!(!s.contains("yellow"));

    assert!(s.contains(&FStr::from_bytes(*b"crisis").unwrap()));
    assert!(s.contains(&FStr::from_bytes(*b"eating").unwrap()));
    assert!(s.contains(&FStr::from_bytes(*b"lucent").unwrap()));
    assert!(!s.contains(&FStr::from_bytes(*b"system").unwrap()));
    assert!(!s.contains(&FStr::from_bytes(*b"unless").unwrap()));
    assert!(!s.contains(&FStr::from_bytes(*b"yellow").unwrap()));
}
