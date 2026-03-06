# Work In Progress

## Judgment notation cleanup

Audit of all `judgment_fn!` bodies in `src/type_system/` found Rust-isms that intrude on the type-theory notation. This punch list tracks the cleanup across sessions.

### ~~Category A: `&` on judgment call arguments~~ ✓ DONE

No formality-core change needed — `impl Upcast<T>` already accepts `&T` via `UpcastFrom<&T>`. Removed ~110 redundant `&` prefixes from judgment call arguments across 10 files. All 485 tests pass.

### Category B: `&` on helper method arguments (~108 instances)

Calls to non-judgment methods: `env.place_ty(&place)`, `NamedTy::new(&name, &sub)`, `live_after.before(&exprs)`, `place.is_prefix_of(&other)`, etc.

| File | Approx count |
|---|---:|
| expressions.rs | ~35 |
| accesses.rs | ~18 |
| statements.rs | ~16 |
| redperms.rs | ~10 |
| classes.rs | ~6 |
| methods.rs | ~5 |
| subtypes.rs | ~4 |
| local_liens.rs | ~3 |
| types.rs | ~3 |
| predicates.rs | ~8 |
| **Total** | **~108** |

**Fix**: Change helper method signatures to accept owned values or `impl Borrow<T>`, or make them take `&self`-style references that auto-deref. Larger effort, per-method.

- [ ] Audit helper method signatures for `&`-removal feasibility
- [ ] Update method signatures and call sites

### Category C: `&` in return position (15 instances)

`=> &env`, `=> (env, &ty)`, `=> (&env, &this_ty)`. Occurs when a judgment returns a value the rule body only holds as `&T`.

| File | Count |
|---|---:|
| expressions.rs | 11 |
| accesses.rs | 2 |
| redperms.rs | 1 |
| statements.rs | 1 |
| **Total** | **15** |

**Fix**: Likely requires macro support for auto-cloning on return, or restructuring rules so the returned value is owned.

- [ ] Determine approach (macro auto-clone vs rule restructuring)
- [ ] Remove `&` from return positions

### Category D: `.clone()` / `Ty::clone(x)` / `Perm::clone(x)` (~50+ instances)

Two sub-patterns:

**D1: Qualified clone through `&Arc<T>` fields** — `Perm::clone(perm1)`, `Ty::clone(ty)`, `Place::clone(place)`. Needed because `.clone()` on `&Arc<T>` gives `Arc<T>`, not `T`. Concentrated in predicates.rs (~25) and redperms.rs (~10).

**D2: Plain `.clone()` on `&T` values** — `ty.clone()`, `perm.clone()`, `env.clone()`, `live_after.clone()`. Needed when constructing enum variants expecting owned values from let-binding results that are `&T`.

| File | Approx count |
|---|---:|
| predicates.rs | ~25 |
| redperms.rs | ~10 |
| expressions.rs | ~8 |
| statements.rs | ~3 |
| subtypes.rs | ~1 |
| type_system.rs | ~1 |
| **Total** | **~50** |

**Fix**: D1 requires grammar changes (remove `Arc` wrapping from `Perm`/`Ty` fields?) or macro support for transparent Arc access. D2 may be addressed by Categories A/C fixes (if variables become owned, no clone needed).

- [ ] Investigate removing Arc wrapping from grammar fields
- [ ] Audit which `.clone()` calls become unnecessary after A/C fixes

### Category E: `&**` double-deref through Arc fields (~20 instances)

When grammar declares `Arc<Ty>` or `Arc<Perm>` and the macro gives `&Arc<T>`, accessing the inner value requires `&**`:

```rust
// Before:
(type_expr(env, live_after, &**rhs) => ...)
(liens(env, &**lhs) => ...)
```

| File | Approx count |
|---|---:|
| expressions.rs | 8 |
| types.rs | 5 |
| predicates.rs | 4 |
| local_liens.rs | 3 |
| statements.rs | 2 |
| **Total** | **~22** |

**Fix**: Same root cause as D1 — the `Arc` wrapping in grammar types. If Arc is removed or the macro auto-derefs, these disappear.

- [ ] Address alongside Category D1 (Arc wrapping)

### Category F: Explicit type annotations on `let` bindings (~13 instances)

Needed for Rust type inference, especially in `for_all...with(acc)` accumulator patterns:

```rust
(let liens: Set<Lien> = Set::new())
(let liens: Set<Lien> = (&liens).union_with(new_liens))
```

| File | Count |
|---|---:|
| local_liens.rs | 8 |
| expressions.rs | 2 |
| accesses.rs | 1 |
| redperms.rs | 1 |
| **Total** | **~13** |

**Fix**: Macro could infer accumulator types from the `with(acc)` initializer, or accept an explicit type on the `with` clause instead of on every `let` rebinding.

- [ ] Determine if macro change can eliminate these

### Category G: `(&acc).method()` accumulator borrows (4 instances, local_liens.rs)

`(&liens).union_with(new_liens)` — needed to avoid consuming the accumulator in `for_all...with` bodies.

**Fix**: Addressed by Category F macro improvements (accumulator handling).

- [ ] Address alongside Category F

### Category H: Iterator chains, imperative blocks, other Rust-isms (~15 instances)

Miscellaneous Rust plumbing inside judgment bodies:

- `.iter().map().collect()` / `.flat_map().collect::<Vec<_>>()` — accesses.rs, classes.rs, expressions.rs, methods.rs, redperms.rs, subtypes.rs (~8)
- `let () = { for ... { ... } Ok::<_, anyhow::Error>(()) }?` imperative blocks — classes.rs (2)
- `tracing::debug!()` inside judgments — expressions.rs (3)
- `.upcast()` type conversions — redperms.rs (3)
- `@` pattern bindings in conclusions — predicates.rs (3)
- `izip!` macro — subtypes.rs (1)

**Fix**: Some may require helper judgments to replace imperative code. Debug logging and upcast may be acceptable. Iterator chains could become `for_all` premises if the macro supports the pattern.

- [ ] Replace imperative blocks in check_field with judgment premises
- [ ] Evaluate which Rust-isms are acceptable vs removable

## Other deferred work

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

All Array[T] operations implemented. Test coverage includes refcount lifecycle, element type variations, ArrayDrop paths, ArrayInitialize, sharing paths, and given array operations. See git history for details.

Remaining gaps: Drop Borrowed element, negative length fault (blocked on grammar).

</details>

<details>
<summary>formality-core all-refs rebase</summary>

Rebased over formality-core PR #246 (all-refs). Updated from `c3108cfa` to `940a1d2e`. Fixed 114 compile errors, all 478 tests pass. Cosmetic cleanup of redundant `&env`/`&live_after` partially done.

</details>
