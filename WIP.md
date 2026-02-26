# Work In Progress

## Completed: Fix `resolve_place` type computation

**Done.** `resolve_place` now delegates type computation to `Env::place_ty` (from the type system) when the place has field projections. This correctly accumulates permissions through projection chains.

### What was done

1. **`env_from_stack_frame`**: Builds a type system `Env` from the interpreter's stack frame. Variable types are enriched with runtime permission info — borrowed/shared flags are mapped to `Ty::ApplyPerm(Perm::Rf/Shared, ...)` wrappers so `place_ty` can thread them through fields.

2. **`resolve_place` uses `place_ty`**: For places with projections (e.g., `r.inner`), the type comes from `env.place_ty(place)`. For bare variables (no projections), the type comes directly from the stack frame. Pointer computation remains interpreter-specific.

3. **`effective_flags`**: Computes effective runtime flags by consulting both the type-level permission (from `ApplyPerm`) and the runtime flags word. Type-level permissions cap the effective flags: `Perm::Rf` → `Borrowed`, `Perm::Shared` → `Shared`.

4. **Display prefix**: `fmt_value` now shows a permission prefix (`ref`, `shared`, etc.) when the type has an `ApplyPerm` wrapper. This only appears for values accessed through permission-wrapped paths.

### Tests

All three TDD tests now pass:
- `give_field_through_borrowed_path` — give through ref produces Borrowed copy, source intact
- `ref_field_through_borrowed_path` — ref through ref produces Borrowed
- `give_field_through_shared_path` — give through shared produces Shared copy with `shared` prefix

Two existing subfield tests updated to show correct `shared` prefix:
- `give_shared_nested_subfield`
- `ref_from_shared_nested_subfield`

## Next: Revisit `resolve_place` / `env_from_stack_frame` design

User has an idea to explore in the next session — may involve rethinking the current approach (enriching variable types with runtime flags via `type_with_runtime_perm` to bridge interpreter ↔ type system).

Current approach uses `Perm::Rf(empty_set)` because the interpreter doesn't track which place was borrowed. Display currently shows `ref` without places.

## Deferred

- [ ] **Doc**: clean up `md/wip/unsafe.md` — remove completed implementation plan, update stale sections, and split content into proper book chapters.
