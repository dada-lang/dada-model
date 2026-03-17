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

pub fn test_interpret(input: &str) -> anyhow::Result<InterpretResult> {
    let program: Arc<Program> = dada_lang::try_term(input)?;
    let ((), _proof_tree) = type_system::check_program(&program).into_singleton()?;
    Ok(run_interpreter(&program))
}

/// Interpret without type-checking first.
/// Useful for testing interpreter behavior on programs the type checker would reject.
pub fn test_interpret_only(input: &str) -> anyhow::Result<InterpretResult> {
    let program: Arc<Program> = dada_lang::try_term(input)?;
    Ok(run_interpreter(&program))
}

fn run_interpreter(program: &Arc<Program>) -> InterpretResult {
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
    ({ $($input:tt)* }, $expect:expr) => {{
        let r = $crate::test_util::test_interpret(stringify!($($input)*))
            .expect("parse/typecheck error");
        assert!(
            r.result.starts_with("Ok:"),
            "unexpected interpreter fault: {}",
            r.result,
        );
        $expect.assert_eq(&r.to_snapshot());
    }};
}

/// Like `assert_interpret!` but skips type-checking.
/// Use this to test interpreter behavior on programs the type checker would reject.
#[macro_export]
macro_rules! assert_interpret_only {
    ({ $($input:tt)* }, $expect:expr) => {{
        let r = $crate::test_util::test_interpret_only(stringify!($($input)*))
            .expect("parse error");
        assert!(
            r.result.starts_with("Ok:"),
            "unexpected interpreter fault: {}",
            r.result,
        );
        $expect.assert_eq(&r.to_snapshot());
    }};
}

/// Like `assert_interpret_only!` but expects the interpreter to fault.
/// Skips type-checking — use this to verify that UB programs are caught at runtime.
/// Panics if the result does not contain "Fault:", preventing UPDATE_EXPECT drift.
#[macro_export]
macro_rules! assert_interpret_fault {
    ({ $($input:tt)* }, $expect:expr) => {{
        let r = $crate::test_util::test_interpret_only(stringify!($($input)*))
            .expect("parse error");
        assert!(
            r.result.starts_with("Fault:"),
            "expected interpreter fault, got: {}",
            r.result,
        );
        $expect.assert_eq(&r.to_snapshot());
    }};
}
