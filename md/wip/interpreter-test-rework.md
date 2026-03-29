# Interpreter Test Rework

## Goal

Every interpreter test should **always run the type checker** and assert its expected outcome (pass or fail) before running the interpreter. Today, `assert_interpret_fault!` and `vec_test!` skip the type checker entirely, which means we don't know whether the type checker accepts or rejects those programs.

The new regime: a single unified `assert_interpret!` macro that takes the program, the expected type-checker outcome (`type: ok` or `type: error(expect_test::expect![[...]])`), and the expected interpreter outcome (`interpret: ok(expect_test::expect![[...]])` or `interpret: fault(expect_test::expect![[...]])`). See the FAQ for details.

All old macros (`assert_interpret_fault!`, `assert_interpret_only!`, `assert_interpret_after_err!`, `vec_test!`) are removed. Every test must declare the type checker's expected verdict.

## Current State

| Macro | What it does | Count |
|---|---|---|
| `assert_interpret!` | type-check ok → interpret ok | 64 |
| `assert_interpret_only!` | skip type-check → interpret ok | 114 |
| `assert_interpret_fault!` (2-arg) | skip type-check → interpret fault | 21 |
| `vec_test!` | skip type-check → interpret ok | 10 |
| `assert_interpret_after_err!` | type-check err (snapshot) → interpret ok | 0 invocations |

### Files with tests that skip the type checker

**`assert_interpret_only!` (114 calls):**
- `src/interpreter/tests/array.rs` — 55 calls. Comment says “type checker's Array rules are simplified stubs.”
- `src/interpreter/tests/place_ops.rs` — 33 calls. Place operation tests that skip type-checking.
- `src/interpreter/tests/mdbook.rs` — 11 calls.
- `src/interpreter/tests/drop_body.rs` — 9 calls (loop/break not supported by type checker).
- `src/interpreter/tests/block_scoped_drops.rs` — 6 calls.
- `src/interpreter/tests/basics.rs` — 2 calls (loop tests).
- `src/interpreter/tests/share.rs` — 1 call.

**`assert_interpret_fault!` (21 calls):**
- `src/interpreter/tests/array.rs` — 11 calls. Runtime UB (e.g., reading uninitialized array slots after drop).
- `src/interpreter/tests/place_ops.rs` — 9 calls. Exercise use-after-give, double-give, etc.
- `src/interpreter/tests/generics.rs` — 1 call. Double-give of Box[Data].

**`vec_test!` (10 calls):**
- `src/interpreter/tests/vector.rs` — 10 calls. All skip type-check because “the type checker doesn't yet fully support the permission patterns Vec uses.”

## The New Macro

Helper functions in `test_util.rs`:

```rust
use std::sync::Arc;

/// Parse input fragments (concatenated), return the program. Panics on parse error.
pub fn parse_program(inputs: &[&str]) -> Arc<Program> {
    let combined: String = inputs.concat();
    dada_lang::try_term(&combined).expect("parse error")
}

/// Run the type checker. Returns Ok(()) or Err(normalized error string).
pub fn check_program_result(program: &Arc<Program>) -> Result<(), String> {
    match type_system::check_program(program).into_singleton() {
        Ok(_) => Ok(()),
        Err(e) => Err(formality_core::test_util::normalize_paths(
            format_error_leaves(&e),
        )),
    }
}

/// Assert the type checker passes. Panics with the error if it fails.
pub fn assert_type_ok(program: &Arc<Program>) {
    if let Err(e) = check_program_result(program) {
        panic!("expected type checker to pass, but it failed:\n{e}");
    }
}

/// Assert the type checker fails. Returns the error string for snapshot comparison.
/// Panics if the type checker passes.
pub fn assert_type_err(program: &Arc<Program>) -> String {
    match check_program_result(program) {
        Ok(()) => panic!("expected type checker to fail, but it passed"),
        Err(e) => e,
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
```

`run_interpreter` must also be made `pub` (it's currently private).

The macro becomes thin dispatch:

```rust
#[macro_export]
macro_rules! assert_interpret {
    // Optional prefix: for injecting shared definitions (e.g., vec_prelude()).
    // Usage: assert_interpret!(prefix: vec_prelude(), { program }, type: ok, interpret: ok(expect));

    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: ok, interpret: ok($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        $crate::test_util::assert_type_ok(&program);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Ok:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};

    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: ok, interpret: fault($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        $crate::test_util::assert_type_ok(&program);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Fault:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};

    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: error($type_expect:expr), interpret: ok($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        let type_err = $crate::test_util::assert_type_err(&program);
        $type_expect.assert_eq(&type_err);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Ok:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};

    ($(prefix: $prefix:expr,)? { $($input:tt)* }, type: error($type_expect:expr), interpret: fault($interp_expect:expr)) => {{
        let program = $crate::test_util::parse_program(&[$($prefix,)? stringify!($($input)*)]);
        let type_err = $crate::test_util::assert_type_err(&program);
        $type_expect.assert_eq(&type_err);
        let r = $crate::test_util::run_interpreter(&program);
        $crate::test_util::assert_interpret_result(&r, "Fault:");
        $interp_expect.assert_eq(&r.to_snapshot());
    }};
}
```

## Plan

### Phase 1: Rewrite `assert_interpret!` and convert existing uses

- [x] Replace the `assert_interpret!` macro in `src/test_util.rs` with the new unified version above.
- [x] Make `run_interpreter` pub.
- [x] Add helper functions: `parse_program`, `check_program_result`, `assert_type_ok`, `assert_type_err`, `assert_interpret_result`.
- [x] Convert all 64 existing `assert_interpret!` calls from the old form:
  ```rust
  assert_interpret!({ program }, expect![[...]]);
  ```
  to the new form:
  ```rust
  assert_interpret!({ program }, type: ok, interpret: ok(expect![[...]]));
  ```
  This is a mechanical text transformation. Other old macros (`assert_interpret_fault!`, `assert_interpret_only!`, `assert_interpret_after_err!`) remain untouched in this commit.

This is a single commit. All tests should pass with no snapshot changes.

**Note:** The original count of 178 `assert_interpret!` was wrong - it included 114 `assert_interpret_only!` calls. The actual `assert_interpret!` count is 64. The `assert_interpret_only!` calls are migrated in Phase 2a (new phase).

### Phase 2a: Migrate `assert_interpret_only!` call sites (one commit per file)

For each existing `assert_interpret_only!`, run the type checker and convert to `assert_interpret!` with the appropriate `type:` tag.

#### Files to migrate

- [ ] `src/interpreter/tests/array.rs` - 55 calls
- [ ] `src/interpreter/tests/place_ops.rs` - 33 calls
- [ ] `src/interpreter/tests/mdbook.rs` - 11 calls
- [ ] `src/interpreter/tests/drop_body.rs` - 9 calls
- [ ] `src/interpreter/tests/block_scoped_drops.rs` - 6 calls
- [ ] `src/interpreter/tests/basics.rs` - 2 calls (includes loop test)
- [ ] `src/interpreter/tests/share.rs` - 1 call

### Phase 2b: Migrate `assert_interpret_fault!` call sites (one commit per file)

For each existing 2-arg `assert_interpret_fault!`, run the type checker and convert to `assert_interpret!` with the appropriate `type:` tag. If the type checker unexpectedly passes, see the FAQ entry on soundness bugs.

#### Files to migrate

- [ ] `src/interpreter/tests/array.rs` - 11 tests
- [ ] `src/interpreter/tests/place_ops.rs` - 9 tests
- [ ] `src/interpreter/tests/generics.rs` - 1 test

### Phase 3: Migrate `vec_test!` call sites

The `vec_test!` macro in `src/interpreter/tests/vector.rs` uses `test_interpret_only`. These are programs the type checker doesn't fully support yet. Each `vec_test!` becomes an `assert_interpret!` with `prefix: vec_prelude()` to inject the shared Vec/Iterator definitions. The `vec_prelude()` helper function stays.

One commit per test:

- [ ] Try running the type checker on each `vec_test!` program.
- [ ] If the type checker passes: convert to `assert_interpret!(prefix: vec_prelude(), { ... }, type: ok, ...)`.
- [ ] If the type checker fails: convert to `assert_interpret!(prefix: vec_prelude(), { ... }, type: error(expect_test::expect![[...]]), ...)`. This documents exactly what the type checker gets wrong, so we can fix it later.

### Phase 4: Final cleanup

- [ ] Remove old macros (`assert_interpret_fault!`, `assert_interpret_only!`, `assert_interpret_after_err!`) and old helpers (`test_interpret_only`, `test_interpret_after_err`).
- [ ] Remove the `vec_test!` macro.
- [ ] Remove stale comments in `array.rs` ("All tests use assert_interpret_only!").
- [ ] Remove stale comment in `basics.rs` ("Uses assert_interpret_only! because the type checker lacks Loop/Break rules").
- [ ] Remove stale comment in `drop_body.rs` about `assert_interpret_only!`.
- [ ] Update `AGENTS.md` test macro descriptions to reflect the new set.
- [ ] Update this WIP doc to mark phases complete.

Every commit keeps the tree green and is independently reviewable.

## Future: Panic vs Fault

Today the interpreter has one failure mode: `Fault`. But not all runtime errors are the same:

- **Fault** = true UB (use-after-move, access of uninitialized memory). The type checker *should* prevent these. A program that type-checks ok but faults is a soundness bug.
- **Panic** = deliberate runtime check (array bounds, integer overflow, etc.). These are expected even in well-typed programs. The type system doesn't prevent them and shouldn't.

We don't implement panic yet, but it's coming. When it arrives, we'd add `interpret: panic(expect)` as a third interpreter-outcome tag in the unified macro. This is a normal, expected test pattern - unlike `fault`, a panic in a well-typed program is not a bug.

For now, some of the current `assert_interpret_fault!` tests (e.g., array bounds checks) are really "panic" tests wearing a "fault" hat. During migration we won't try to distinguish them - that's a separate future change.

## FAQ

### Q: What if a fault test passes the type checker?

During migration, some `assert_interpret_fault!` tests may turn out to pass the type checker (i.e., `type: ok, interpret: fault(...)`). This means either:
- The type system has a **soundness gap** (it should reject the program but doesn't), or
- The test is really a **future-panic** test (e.g., array bounds), which the type system correctly accepts.

We don't have a panic mechanism yet, so for now treat every such case as a **soundness bug**. Use `type: ok, interpret: fault(...)` in the migrated test, add a `// BUG:` comment, and collect these in a list at the bottom of this doc so we can track and fix them.

### Q: Why one macro instead of many?

We replace `assert_interpret!`, `assert_interpret_fault!`, `assert_interpret_only!`, `assert_interpret_after_err!`, and `vec_test!` with a single `assert_interpret!` macro. It takes three arguments:

1. The program.
2. The expected type-checker outcome: `type: ok` or `type: error(expect![[...]])`.
3. The expected interpreter outcome: `interpret: ok(expect![[...]])` or `interpret: fault(expect![[...]])`.

This covers all four combinations:

```rust
// normal: type-checks, runs fine
assert_interpret!({ program }, type: ok, interpret: ok(expect![[...]]));

// UB test: type checker catches it, interpreter faults
assert_interpret!({ program }, type: error(expect![[...]]), interpret: fault(expect![[...]]));

// type system gap: type checker rejects, but actually runs fine
assert_interpret!({ program }, type: error(expect![[...]]), interpret: ok(expect![[...]]));

// soundness bug or future-panic: type checker accepts, interpreter faults
assert_interpret!({ program }, type: ok, interpret: fault(expect![[...]]));
```

`type: ok` has no snapshot (just pass/fail). The interpret side always has a snapshot.

Critically, `UPDATE_EXPECT=1` can refresh the *contents* of `expect!` snapshots but **cannot flip** `ok` ↔ `error` or `ok` ↔ `fault`. Those structural tags are part of the macro invocation, not snapshot data. This prevents silent drift where a test changes category without anyone noticing.

## Non-Goals

- We are NOT changing the type system tests (`src/type_system/tests/`). Those use `assert_ok!`/`assert_err!` and don't involve the interpreter.
- We are NOT fixing type system gaps discovered during migration (just documenting them via the error snapshots).
- We are NOT implementing the panic/fault distinction yet - just documenting it for future work.
