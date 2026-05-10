use fstr::FStr;

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
