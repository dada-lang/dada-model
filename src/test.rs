pub fn test_eq(item: impl std::fmt::Debug, expect: expect_test::Expect) {
    let item = format!("{:?}", item);
    let item = normalize_paths(&item);

    // workaround a bug in expect-test...it seems to have trouble with newlines
    let item = item.trim();

    expect.assert_eq(&item)
}

/// Detects path/line/column patterns like `src/blah/foo.rs:22:33` in the string and replace it
/// with a normalized path like `file.rs:LL:CC`.
fn normalize_paths(s: &str) -> String {
    let re = regex::Regex::new(r"\(src/[^:]+:\d+:\d+\)").unwrap();
    re.replace_all(s, "(src/file.rs:LL:CC)").to_string()
}
