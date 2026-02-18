use std::sync::Arc;

use formality_core::judgment::{FailedJudgment, ProofTree};
use formality_core::Fallible;

use crate::dada_lang;
use crate::grammar::Program;
use crate::interpreter::Interpreter;
use crate::type_system;

pub fn test_program_ok(input: &str) -> Fallible<ProofTree> {
    let program: Arc<Program> = dada_lang::try_term(input)?;
    let ((), proof_tree) = type_system::check_program(&program).into_singleton()?;
    Ok(proof_tree)
}

pub fn test_interpret(input: &str) -> anyhow::Result<(String, Vec<String>)> {
    let program: Arc<Program> = dada_lang::try_term(input)?;
    let ((), _proof_tree) = type_system::check_program(&program).into_singleton()?;
    let mut interp = Interpreter::new(&program);
    let result = interp.interpret()?;
    let result_str = interp.display_value(result);
    let output_lines: Vec<String> = interp
        .output()
        .lines()
        .map(|l| l.to_string())
        .collect();
    Ok((result_str, output_lines))
}

/// Format an error, extracting just the leaf failures if it contains a FailedJudgment.
/// Walks the anyhow error chain to find a FailedJudgment even if wrapped in context
/// (e.g., by fn_error_context).
pub fn format_error_leaves(e: &anyhow::Error) -> String {
    // Walk the chain of errors to find a FailedJudgment
    for cause in e.chain() {
        if let Some(failed) = cause.downcast_ref::<Box<FailedJudgment>>() {
            return failed.format_leaves();
        }
        if let Some(failed) = cause.downcast_ref::<FailedJudgment>() {
            return failed.format_leaves();
        }
    }
    // If no FailedJudgment found, fall back to debug format
    format!("{e:?}")
}

/// Check if `output` matches `pattern`, where `*` in the pattern
/// matches any sequence of non-`)` characters (useful for skipping
/// file paths and line numbers in error messages).
pub fn glob_match(output: &str, pattern: &str) -> bool {
    let regex_str = pattern
        .split('*')
        .map(|part| regex::escape(part))
        .collect::<Vec<_>>()
        .join("[^)]*");
    regex::Regex::new(&regex_str).unwrap().is_match(output)
}

#[macro_export]
macro_rules! assert_ok {
    ({ $($input:tt)* }) => {{
        let _ = $crate::test_util::test_program_ok(stringify!($($input)*)).expect("expected program to pass");
    }};

    ($input:expr) => {{
        let _ = $crate::test_util::test_program_ok($input).expect("expected program to pass");
    }};
}

#[macro_export]
macro_rules! assert_err {
    ({ $($input:tt)* }, $expect:expr) => {{
        let result = $crate::test_util::test_program_ok(stringify!($($input)*));
        match result {
            Ok(v) => panic!("expected `Err`, got `Ok`:\n{v:?}"),
            Err(e) => {
                let output =
                    formality_core::test_util::normalize_paths($crate::test_util::format_error_leaves(&e));
                $expect.assert_eq(&output);
            }
        }
    }};

    ($input:expr, $expect:expr) => {{
        let result = $crate::test_util::test_program_ok($input);
        match result {
            Ok(v) => panic!("expected `Err`, got `Ok`:\n{v:?}"),
            Err(e) => {
                let output =
                    formality_core::test_util::normalize_paths($crate::test_util::format_error_leaves(&e));
                $expect.assert_eq(&output);
            }
        }
    }};
}

#[macro_export]
macro_rules! assert_err_str {
    ({ $($token:tt)* }, $($expected_pattern:expr),+ $(,)?) => {{
        $crate::assert_err_str!(stringify!($($token)*), $($expected_pattern),+);
    }};

    ($input:expr, $($expected_pattern:expr),+ $(,)?) => {{
        let result = $crate::test_util::test_program_ok($input);
        match result {
            Ok(v) => panic!("expected `Err`, got `Ok`:\n{v:?}"),
            Err(e) => {
                let output = $crate::test_util::format_error_leaves(&e);
                $(
                    assert!(
                        $crate::test_util::glob_match(&output, $expected_pattern),
                        "error output did not match {:?}\n\nactual error:\n{output}",
                        $expected_pattern,
                    );
                )+
            }
        }
    }};
}

#[macro_export]
macro_rules! assert_interpret {
    // With print lines: assert_interpret!({...}, print "a", print "b", return "result")
    ({ $($input:tt)* }, $(print $output_line:expr,)* return $expected:expr) => {{
        let (result, output_lines) = $crate::test_util::test_interpret(stringify!($($input)*))
            .expect("expected program to type-check and interpret successfully");
        let expected_lines: Vec<&str> = vec![$($output_line),*];
        assert_eq!(output_lines, expected_lines, "interpreter output did not match");
        assert_eq!(result, $expected, "interpreter result did not match");
    }};
}
