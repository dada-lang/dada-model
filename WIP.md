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
