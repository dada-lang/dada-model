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

**Status:** ✅ All fixed — test bugs. Every test stored `shared T` values into array slots or class fields typed as bare `T` (= `given T`). Since `shared` is not a subtype of `given`, the type checker correctly rejected them. Fixes: changed element/field types to `shared T` where shared values are stored; fixed access permissions (`given` → `shared`) when reading from shared arrays; fixed return type mismatches.

### `variance_predicate { kind: relative, parameter: !ty_0 }` — 10 tests

All in vector.rs. The Vec class's `push` method has a universally quantified type parameter `!ty_0` that the type checker can't prove is `relative`. This is a known limitation — the type checker doesn't yet fully support the permission patterns Vec uses.

**vector.rs (10):** All 10 vec tests.

**Status:** ✅ Fixed — type system bug. `check_method` added variance assumptions (relative/atomic) for method-level parameters but not class-level parameters. Similarly, `check_drop_body` had no variance assumptions at all. Fix: pass class-level universal vars (`substitution`) into `check_method` and `check_drop_body`, and add variance assumptions for them alongside method vars. Also added `where T is relative` to Iterator class (legitimately needed for its `vec: P Vec[T]` field).

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

**Status:** ✅ Deleted — test was wrong. The program stuffed a `ref` into an owned class field, creating a `Flags::Borrowed` subfield inside an owned allocation — a scenario that can't arise in well-typed code. The type checker correctly rejects the program (`given is mut` is NOT supposed to be provable). The interpreter edge case being tested (share skips borrowed subfields) is unreachable in practice.

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

## Completed

- [x] Unified test macro rework (see `md/wip/interpreter-test-rework.md`)
- [x] Fixed 14 return-type bugs in test programs (tests returning shared values declared non-shared return types)
- [x] Categorized all 25 remaining `type: error, interpret: ok` tests by root cause
- [x] Fixed all 11 `prove_copy_predicate` tests — all were test bugs (shared values stored into `given`-typed positions)

## Current Inventory: 3 remaining `type: error, interpret: ok`

- **3 loop tests** — known type system gap (no loop/break rules)

## Next Steps

- [x] ~~Investigate variance predicate bug~~ — Fixed: class-level vars now get variance assumptions in methods and drop bodies
- [ ] Loop/break type rules (3 tests) — deferred to future type system work
