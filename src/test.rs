use std::sync::Arc;

use formality_core::Fallible;

use crate::{grammar::Program, type_system::check_program};

pub fn test_eq(item: impl std::fmt::Debug, expect: expect_test::Expect) {
    let item = format!("{:?}", item);
    let item = normalize_paths(&item);

    // workaround a bug in expect-test...it seems to have trouble with trailing newlines
    let item = item.trim();

    expect.assert_eq(&item)
}

/// Detects path/line/column patterns like `src/blah/foo.rs:22:33` in the string and replace it
/// with a normalized path like `file.rs:LL:CC`.
fn normalize_paths(s: &str) -> String {
    let re = regex::Regex::new(r"\(src/[^:]+:\d+:\d+\)").unwrap();
    re.replace_all(s, "(src/file.rs:LL:CC)").to_string()
}

pub fn check_program_errs(
    program: &Arc<Program>,
    expected_err: expect_test::Expect,
) -> Fallible<()> {
    test_eq(check_program(program).unwrap_err(), expected_err);
    Ok(())
}
