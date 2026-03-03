# Work In Progress

## Completed: Split TypedValue into separate Value/Type tracking

**Done.** The interpreter now stores runtime values (Pointer) in the StackFrame and static types (Ty) in `self.env: Env`, mirroring the eventual compiled representation where types are erased at runtime.

### What was done

1. **StackFrame**: Changed `variables: Map<Var, TypedValue>` to `variables: Map<Var, Pointer>`. Runtime values are just pointers; types live in `self.env`.

2. **call_method**: Saves/restores `self.env` around method calls using `std::mem::replace` with a fresh `Env::new(...)`. Pushes `this` + input params into both frame (pointer) and env (type). Cleanup iterates frame vars, gets type from env, frees, then restores saved env.

3. **Let statement**: Splits the TypedValue — stores pointer in frame, pushes type into env via `push_local_variable`.

4. **Place expr result types**: Computes result types following `access_ty` rules:
   - Give: result type = place type (passthrough from `place_ty`)
   - Ref: result type = `Ty::apply_perm(Perm::rf(set![place]), place_ty.strip_perm())`
   - Share: result type = `Ty::apply_perm(Perm::Shared, ty.strip_perm())`
   - `Perm::Given` is treated as identity (no wrapper created)

5. **resolve_place simplified**: Uses `self.env.place_ty()` directly. Deleted `env_from_stack_frame` and `type_with_runtime_perm` bridge code entirely.

6. **effective_flags**: Caps runtime flags with type-level permission from `ApplyPerm` wrapper.

7. **Display**: `fmt_value` shows full permission prefix (`{perm:?}`) when type has `ApplyPerm` wrapper, e.g., `ref [d] Data { ... }`.

### Tests

All 299 tests pass. Through-path tests show correct permission prefixes:
- `give_field_through_borrowed_path` — `ref [r] Inner { flag: Borrowed, value: 10 }`
- `ref_field_through_borrowed_path` — `ref [r.inner] Inner { flag: Borrowed, value: 10 }`
- `give_field_through_shared_path` — `shared Inner { flag: Shared, value: 10 }`

## Deferred

- [ ] **Doc**: clean up `md/wip/unsafe.md` — remove completed implementation plan, update stale sections, and split content into proper book chapters.
- [x] **Doc**: Add Array[T] content to the interpreter chapter (md/interpreter.md) — array layout diagrams, all five operations, copy-vs-move element semantics, sharing/refcounting (share_op vs convert_to_shared), given array moves, drop with refcount-to-zero cleanup. Seven example-driven tests added to mdbook.rs.
- [x] **Interpreter**: Add `Word::RefCount` and `Word::Capacity` variants so `read_refcount`/`check_array_bounds` can fault on non-refcount/non-capacity integers (hardens UB detection for fuzzing).
- [x] **Interpreter**: ArrayNew parameter validation — already handled by `extract_array_element_ty`.
- [x] **Interpreter**: ArrayGet → ArrayGive, dispatch on element flags like `place.give` (Given→move, Shared→copy+share_op, Borrowed→copy).
- [x] **Interpreter**: Unify `drop_given` and `drop_shared` into `drop_owned_value`.
- [ ] **Interpreter**: Add a `validate` function that checks structural invariants on values — e.g., given array has refcount 1, no unexpected uninitialized words in initialized values, etc. Call before operations to catch invariant violations early.
- [x] **Interpreter**: Audit type matches for exhaustive enumeration. Made `has_flags`, `share_op`, `drop_owned_value`, `fmt_value`, Perm match in `resolve_place`, and Flags match in place eval all exhaustive. Left `_` only for error bail-outs (field access on non-class, method call on non-class) where all non-matching types are uniformly errors.
- [x] **Interpreter**: Extract `effective_flags` method — consolidates the "outer permission flags override inner runtime flags" logic from place expression, ArrayGive, and ArrayDrop into a single method. Fixes bug where shared arrays' elements were moved instead of copied because `convert_to_shared` only flips outermost flags.

## Array[T] Test Coverage Gaps

### Refcount lifecycle
- [x] Shared array survives after original dropped (`shared_array_survives_after_original_dropped`)
- [x] Refcount reaches zero → backing allocation freed (`refcount_reaches_zero_frees_allocation`)
- [x] Class-with-array-field: dropping class drops array (`nested_array_in_class_field`)
- [x] `Array[Array[T]]` — nested arrays, refcount interactions on get/drop (`nested_array_create_and_capacity`, `nested_array_give_inner_from_shared_outer`, `nested_array_drop_inner_decrements_refcount`, `nested_array_all_refs_freed`)
- [x] Multiple references to same array — refcount tracks all refs (`shared_array_two_refs_both_usable`, `shared_array_three_refs_drop_two`, `shared_array_all_refs_dropped_frees`)

### Element type variations
- [x] `Array[SharedClass]` — shared class elements, no flags word per element (`array_of_shared_class_elements`)
- [x] `Array[Array[T]]` — nested arrays, refcount interactions on get/drop (see above)
- [x] Array of class with nested field — recursive drop (`array_of_class_recursive_drop`)
- [x] `shared Array[Array[Data]]` — read Data through outer copy and inner var (`shared_outer_array_of_data_arrays`)
- [x] `Array[shared Array[Data]]` — read Data through both paths (`array_of_shared_inner_arrays`)
- [x] `shared Array[shared Array[Data]]` — all three copies read Data independently (`shared_array_of_shared_arrays`, `shared_array_of_shared_arrays_drop_cascade`)

### ArrayDrop paths
- [x] Drop a Shared element (should `drop_shared`, decrement inner refcount) (`array_drop_shared_element_decrements_refcount`, `array_drop_shared_class_element`)
- [ ] Drop a Borrowed element
- [x] `array_drop` out of bounds → fault (`array_drop_out_of_bounds`)
- [x] `array_drop` on uninitialized slot → fault (`array_drop_uninitialized_faults`)

### ArrayInitialize
- [x] Initialize with class elements containing arrays (ownership transfer of nested refcounted values) (`array_initialize_class_with_array_field`, `array_drop_class_with_array_field`)

### Edge cases
- [ ] `array_new[Int](-1)` → fault (negative length) — **blocked**: no subtraction operator in grammar
- [x] `array_new[Int](0)` → zero-length array (`array_new_zero_length`, `array_zero_length_access_faults`)

### Sharing paths
- [x] `a.ref` on shared array (should trigger share_op) (`ref_on_shared_array_increments_refcount`)
- [x] `convert_to_shared` on array that's a field inside a class (`share_class_containing_array`)

### Given array operations
- [x] Given array give moves and uninitializes source (`given_array_give_moves`, `given_array_double_give_faults`)
- [x] Given array give class element moves out (`given_array_give_class_moves_out`)
- [x] Shared array give class element copies with shared semantics (`shared_array_give_class_is_shared_copy`)
