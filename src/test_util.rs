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

/// Result of running the interpreter.
pub struct InterpretResult {
    pub result: String,
    pub output_lines: Vec<String>,
    pub alloc_lines: Vec<String>,
}

impl InterpretResult {
    /// Produce a snapshot string for expect_test comparison.
    /// Format:
    ///   Output: <line>              (one per print output line)
    ///   Result: <value>
    ///   Alloc 0x00: [words...]      (live allocations only, hex-indexed)
    ///   Alloc 0x02: [words...]
    pub fn to_snapshot(&self) -> String {
        let mut lines = Vec::new();
        for output_line in &self.output_lines {
            lines.push(format!("Output: {output_line}"));
        }
        lines.push(format!("Result: {}", self.result));
        for alloc_line in &self.alloc_lines {
            lines.push(format!("Alloc {alloc_line}"));
        }
        lines.join("\n")
    }
}

/// Parse input fragments (concatenated), return the program. Panics on parse error.
pub fn parse_program(inputs: &[&str]) -> Arc<Program> {
    let combined: String = inputs.concat();
    dada_lang::try_term(&combined).expect("parse error")
}

/// Assert the type checker passes. Panics with the error if it fails.
pub fn assert_type_ok(program: &Arc<Program>) {
    match type_system::check_program(program).into_singleton() {
        Ok(_proof_tree) => {}
        Err(e) => {
            panic!("expected type checker to pass, but it failed:\n{e}");
        }
    }
}

/// Assert the type checker fails. Returns the error string for snapshot comparison.
/// Panics if the type checker passes.
pub fn assert_type_err(program: &Arc<Program>) -> String {
    match type_system::check_program(program).into_singleton() {
        Ok(proof_tree) => panic!("expected type checker to fail, but it passed: {proof_tree:?}"),
        Err(e) => {
            println!("full error:\n\n{e}");
            formality_core::test_util::normalize_paths(e.format_leaves())
        }
    }
}

/// Assert the interpreter result starts with the given prefix ("Ok:" or "Fault:").
pub fn assert_interpret_result(r: &InterpretResult, expected_prefix: &str) {
    assert!(
        r.result.starts_with(expected_prefix),
        "expected interpreter result starting with {expected_prefix:?}, got:\n{}",
        r.to_snapshot(),
    );
}

pub fn run_interpreter(program: &Arc<Program>) -> InterpretResult {
    let mut interp = Interpreter::new(program);
    let result = interp.interpret();
    let result_str = result
        .and_then(|v| interp.display_value(&crate::type_system::env::Env::new(program.clone()), &v))
        .map(|s| format!("Ok: {s}"))
        .unwrap_or_else(|e| format!("Fault: {e:?}"));
    let output_lines: Vec<String> = interp.output().lines().map(|l| l.to_string()).collect();
    let alloc_lines = interp.dump_heap();
    InterpretResult {
        result: result_str,
        output_lines,
        alloc_lines,
    }
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
macro_rules! assert_interpret {
    // type: ok, interpret: ok
    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: ok, interpret: ok($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        $crate::test_util::assert_type_ok(&program);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Ok:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};

    // type: ok, interpret: fault
    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: ok, interpret: fault($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        $crate::test_util::assert_type_ok(&program);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Fault:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};

    // type: error, interpret: ok
    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: error($type_expect:expr), interpret: ok($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        let type_err = $crate::test_util::assert_type_err(&program);
        $type_expect.assert_eq(&type_err);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Ok:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};

    // type: error, interpret: fault
    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: error($type_expect:expr), interpret: fault($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        let type_err = $crate::test_util::assert_type_err(&program);
        $type_expect.assert_eq(&type_err);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Fault:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};
}
