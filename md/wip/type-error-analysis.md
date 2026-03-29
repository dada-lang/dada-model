# Type Error Analysis

## Goal

Using the unified `assert_interpret!` macro, systematically analyze every `type: error, interpret: ok` test — programs the type checker rejects but that run correctly. For each, determine whether:

1. **The test is wrong** (e.g., wrong return type) — fix the test so it passes type-checking.
2. **The type system has a gap** — document the root cause for future type system work.

We do NOT change type system rules during this work.

## Current Inventory

As of the test rework, there are **25** tests with `type: error, interpret: ok`:

### `prove_copy_predicate { p: given }` — 11 tests

The type checker cannot prove `given is copy`. These fail mid-body, typically when dealing with shared arrays or constructors that mix shared and given values.

**array.rs (10):**
- `array_write_overwrites_shared_array` — writing shared array into array-of-arrays
- `nested_array_give_inner_from_shared_outer` — nested shared array access
- `nested_array_drop_inner_decrements_refcount` — nested shared array drop
- `shared_outer_array_of_data_arrays` — shared outer array of Data arrays
- `array_of_shared_inner_arrays` — array containing shared inner arrays
- `shared_outer_give_inner_survives_outer_drop` — inner array survives outer drop
- `shared_array_of_shared_arrays` — shared array of shared arrays
- `shared_array_of_shared_arrays_drop_cascade` — cascade drop of shared arrays
- `array_drop_shared_element_decrements_refcount` — drop shared class element
- `array_give_p_shared` — array_give with P=shared

**drop_body.rs (1):**
- `is_last_ref_per_allocation` — constructing class with shared array field

**Status:** Not yet analyzed in detail. Need to determine if these are test bugs or real type system gaps.

### `variance_predicate { kind: relative, parameter: !ty_0 }` — 10 tests

All in vector.rs. The Vec class's `push` method has a universally quantified type parameter `!ty_0` that the type checker can't prove is `relative`. This is a known limitation — the type checker doesn't yet fully support the permission patterns Vec uses.

**vector.rs (10):** All 10 vec tests.

**Status:** Known type system gap. These all fail on the same Vec class definition, not on the individual test programs.

### `type_statement` for `loop` — 3 tests

The type checker has no rules for loop/break statements.

**basics.rs (1):**
- `loop_body_value_is_freed`

**block_scoped_drops.rs (2):**
- `block_early_break_drops_locals`
- `loop_break_drops_locals`

**Status:** Known type system gap (no loop/break rules).

### `prove_mut_predicate { p: given }` — 1 test

The type checker cannot prove `given is mut`. The `.share` expression needs `prove_is_shareable`, which tries `prove_is_mut(perm)`, but there's no rule for `Perm::Given`.

**share.rs (1):**
- `share_skips_borrowed_subfield`

**Status:** Identified root cause: missing `given is mut` rule in `prove_mut_predicate`. Fix deferred to type system work.

## Completed

- [x] Unified test macro rework (see `md/wip/interpreter-test-rework.md`)
- [x] Fixed 14 return-type bugs in test programs (tests returning shared values declared non-shared return types)
- [x] Categorized all 25 remaining `type: error, interpret: ok` tests by root cause

## Also Found: Soundness Gaps (`type: ok, interpret: fault`)

These tests pass type-checking but fault at runtime:

**Future-panic (type system correctly accepts; runtime bounds/init checks):**
- `array_give_uninitialized_faults`
- `array_give_out_of_bounds`
- `array_write_out_of_bounds`
- `array_drop_out_of_bounds`
- `array_drop_uninitialized_faults`
- `array_zero_length_access_faults`

**Soundness gaps (type system should reject but doesn't):**
- `array_drop_element` — use after array_drop
- `array_drop_shared_class_element` — use after array_drop
- `array_drop_p_given_range` — use after array_drop

## Next Steps

- [ ] Analyze the 11 `prove_copy_predicate` tests in detail — are any fixable as test bugs (like the return-type fixes), or are they all real type system gaps?
- [ ] For real type system gaps, document the specific missing rule or logic needed.
