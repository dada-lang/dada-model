# Work In Progress

Current implementation plan for the interpreter and unsafe primitives.
See `md/wip/unsafe.md` for the full design spec.

## Current: Step 6 — Implement reference counting for arrays

- [ ] **Doc**: add section to array chapter on sharing and ref counting
- [ ] **Tests first**: shared array survives after original dropped, array freed when last reference dropped, elements recursively dropped on array free
- [ ] Share operation increments array ref count
- [ ] Drop-shared decrements ref count, frees when zero

**Goal: array ref counting works correctly**

## Deferred

- [ ] **`share_op` should skip Borrowed/Uninitialized fields**: Code recurses into all fields unconditionally, but spec says "for a borrowed class | mut-ref, no-op". Deferred to after Array[T] — will have natural test scenarios with array fields vs borrowed fields.
- [ ] **Doc**: expand `md/wip/unsafe.md` into a proper chapter — motivating example (building a simple Vec), then walk through ArrayNew/Initialize/Get/Drop

## Completed

- [x] Step 1: Remove PointerOps
- [x] Step 2: Add `size_of[T]()`
- [x] Step 3: Restructure interpreter memory model
- [x] Step 4: Implement place operations (give/ref/drop)
- [x] Step 4b: Doc/code review cleanup (share_op ordering, Outcome enum for control flow)
- [x] Step 5: Add Array[T] — grammar, type system stubs, interpreter, 16 tests
  - `TypeName::Array`, 5 Expr variants (ArrayNew/Capacity/Get/Drop/Initialize)
  - `Word::Array(Pointer, Flags)` — single-word representation with embedded flags
  - `size_of(Array[T])` = 1, `has_flags` = No (flags embedded in Word::Array)
  - Array is a share class (`ClassPredicate::Share`)
  - Tests share array after creation for multi-use: `let a = array_new[Int](3).share;`
  - share_op/drop for arrays are no-ops (refcount deferred to Step 6)
  - Fixed `Expr::Share` to use `write_flags()` instead of direct `write_word()` for array compatibility
