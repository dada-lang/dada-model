# Work In Progress

Current implementation plan for the interpreter and unsafe primitives.
See `md/wip/unsafe.md` for the full design spec.

## Deferred

- [x] **`convert_to_shared` should skip Borrowed/Uninitialized fields**: Added early return when flags word is `Borrowed` or `Uninitialized` before recursing into sub-fields. Added `share_skips_borrowed_subfield` interpreter test that demonstrates the bug (Inner inside Borrowed Mid was incorrectly flipped to Shared).
- [x] **Loop body value leak**: `Statement::Loop` now calls `free` on `Outcome::Value` from each iteration. Added `loop_body_value_is_freed` interpreter test that demonstrates the fix (a loop producing `new Point(1,2)` on non-breaking iterations — the Point allocation was leaked before, now freed).
- [ ] **FREE semantics for values with reference-counted sub-fields**: `Reassign`, `ArrayInitialize` (and `Expr::New` for array fields) call `free` after a bitwise copy, which would double-drop any Array field. Deferred until classes-with-array-fields are tested.
- [ ] **Doc**: expand `md/wip/unsafe.md` into a proper chapter — motivating example (building a simple Vec), then walk through ArrayNew/Initialize/Get/Drop

## Completed

- [x] Step 1: Remove PointerOps
- [x] Step 2: Add `size_of[T]()`
- [x] Step 3: Restructure interpreter memory model
- [x] Step 4: Implement place operations (give/ref/drop)
- [x] Step 4b: Doc/code review cleanup (share_op ordering, Outcome enum for control flow)
- [x] Step 5: Add Array[T] — grammar, type system stubs, interpreter, 16 tests
  - `TypeName::Array`, 5 Expr variants (ArrayNew/Capacity/Get/Drop/Initialize)
  - Two-word representation: `[Word::Flags, Word::Pointer]` (same layout as classes)
  - `size_of(Array[T])` = 2, `has_flags` = Yes
  - Array is a share class (`ClassPredicate::Share`)
  - Tests share array after creation for multi-use: `let a = array_new[Int](3).share;`
- [x] Step 5b: Word::Uninitialized audit — flags word invariant, uninitialize scrubs all words
- [x] Step 5c: Two-word layout refactor — uniform `[Flags, Pointer]` representation for arrays
- [x] Step 6: Reference counting for arrays
  - Split `share_op` into `convert_to_shared` (in-place flag flip, used by Expr::Share) and `share_op` (duplication accounting, used by Access::Gv/Rf on Shared)
  - `share_op` increments array refcount when a shared copy is made
  - `drop_given`/`drop_shared` decrement refcount; when zero, recursively drop initialized elements and free allocation
  - `drop_array` helper handles both Given and Shared drop paths
  - Allocation freed by clearing `alloc.data` — accessing freed allocation would read out-of-bounds
  - Array ops drop their array argument via `drop_temp` to avoid temporary refcount leaks
  - 22 interpreter tests (6 new refcounting tests)
- [x] Step 6b: Heap snapshot infrastructure — `dump_heap()` + `InterpretResult::to_snapshot()`, tests use `expect_test`
- [x] Step 7: FREE operation — uniform temporary cleanup
  - `free(tv)` = ownership-semantic drop + scrub all words to `Word::Uninitialized`
  - `Statement::Let` ownership moves into stack frame (returns unit, not the tv)
  - `call_method` frees remaining stack frame variables at end-of-scope (cleanup of `this` + args)
  - Array ops (`ArrayGet`, `ArrayDrop`, `ArrayInitialize`) free their index and value temporaries
  - All 292 tests pass; snapshots updated to reflect freed allocations
