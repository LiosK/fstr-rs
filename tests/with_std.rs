use fstr::FStr;

/// Tests `Hash` and `Borrow` implementations using `HashSet`.
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
