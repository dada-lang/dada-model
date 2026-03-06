# Work In Progress

## Deferred work

- [ ] **Doc**: clean up `md/wip/unsafe.md` — remove completed implementation plan, update stale sections, split into book chapters
- [ ] **Interpreter**: Add `validate` function for structural invariant checks (given array refcount=1, no unexpected uninitialized words, etc.)
- [ ] **Interpreter**: ArrayDrop of Borrowed element (test coverage gap)
- [ ] **Interpreter**: `array_new[Int](-1)` fault test — blocked on no subtraction operator in grammar
- [ ] **Rename**: `Access::Mv` → TBD (last permission rename)
- [ ] **Type system**: Investigate `prove_is_mut` succeeding on `ref[mut_place]` (FIXME in tests)
- [ ] **Type system**: Investigate whether `prove_is_shareable` precondition on cancellation is reachable in concrete programs

## Completed work (archived)

<details>
<summary>Split TypedValue into separate Value/Type tracking</summary>

The interpreter now stores runtime values (Pointer) in the StackFrame and static types (Ty) in `self.env: Env`, mirroring the eventual compiled representation where types are erased at runtime.

1. StackFrame: `Map<Var, TypedValue>` → `Map<Var, Pointer>`
2. call_method: saves/restores `self.env` around calls
3. Let statement: splits TypedValue — pointer in frame, type in env
4. Place expr result types follow `access_ty` rules
5. resolve_place uses `self.env.place_ty()` directly
6. effective_flags caps runtime flags with type-level permission
7. Display shows full permission prefix

</details>

<details>
<summary>Array[T] implementation and test coverage</summary>

All Array[T] operations implemented. Test coverage includes refcount lifecycle, element type variations, ArrayDrop paths, ArraySet, sharing paths, and given array operations. See git history for details.

Remaining gaps: Drop Borrowed element, negative length fault (blocked on grammar).

</details>

<details>
<summary>formality-core all-refs rebase</summary>

Rebased over formality-core PR #246 (all-refs). Updated from `c3108cfa` to `940a1d2e`. Fixed 114 compile errors, all 478 tests pass. Cosmetic cleanup of redundant `&env`/`&live_after` partially done.

</details>
