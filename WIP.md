# Work In Progress

Current implementation plan for the interpreter and unsafe primitives.
See `md/wip/unsafe.md` for the full design spec.

## Current: Step 5 — Add Array[T] to grammar and implement operations

- [ ] **Doc**: expand `md/wip/unsafe.md` into a proper chapter — motivating example (building a simple Vec), then walk through ArrayNew/Initialize/Get/Drop
- [ ] **Tests first**: write interpreter tests — create array, initialize elements, read them back, drop elements. Test out-of-bounds faults. Test uninitialized read faults
- [ ] Add `TypeName::Array` (with one type parameter `T`)
- [ ] Add 5 Array expression variants: `ArrayNew[T](expr)`, `ArrayCapacity[T](expr)`, `ArrayGet[T](expr, expr)`, `ArrayDrop[T](expr, expr)`, `ArrayInitialize[T](expr, expr, expr)`
- [ ] Add Array keyword entries
- [ ] Add type-checking rules for all 5 operations
- [ ] Add match arms in type system (`env.rs`, `liveness.rs`, `places.rs`, `types.rs`)
- [ ] Interpreter: `ArrayNew[T](length)` — allocate `[Int(1), Int(length), Uninitialized...]`
- [ ] Interpreter: `ArrayCapacity[T](array)` — read length word
- [ ] Interpreter: `ArrayInitialize[T](array, index, value)` — write element at computed offset
- [ ] Interpreter: `ArrayGet[T](array, index)` — read element via give semantics
- [ ] Interpreter: `ArrayDrop[T](array, index)` — recursively drop element, mark slot uninitialized
- [ ] Add `Word::Array(Pointer)` variant

**Goal: arrays work end-to-end**

## Next: Step 6 — Implement reference counting for arrays

- [ ] **Doc**: add section to array chapter on sharing and ref counting
- [ ] **Tests first**: shared array survives after original dropped, array freed when last reference dropped, elements recursively dropped on array free
- [ ] Share operation increments array ref count
- [ ] Drop-shared decrements ref count, frees when zero

**Goal: array ref counting works correctly**

## Deferred

- [ ] **`share_op` should skip Borrowed/Uninitialized fields**: Code recurses into all fields unconditionally, but spec says "for a borrowed class | mut-ref, no-op". Deferred to after Array[T] — will have natural test scenarios with array fields vs borrowed fields.

## Completed

- [x] Step 1: Remove PointerOps
- [x] Step 2: Add `size_of[T]()`
- [x] Step 3: Restructure interpreter memory model
- [x] Step 4: Implement place operations (give/ref/drop)
- [x] Step 4b: Doc/code review cleanup (share_op ordering, Outcome enum for control flow)
