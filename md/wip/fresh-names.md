# Fresh names and block-scoped drops

## Problem 1: `is_mut_ref_type` divergence

The interpreter's `is_mut_ref_type` uses structural pattern matching instead of the type system's `prove_is_mut` judgment. This divergence exists because `prove_is_mut` on `Perm::Mt(places)` resolves each place's type via `env.place_ty(place)`, but inside a method body the places (e.g., `v` in `mut[v]`) refer to the calling context and are not in the method's env.

Example: calling `v.mut.push[mut[v]](...)` produces a receiver of type `mut[v] Vec[T]`. The method's `self` has that type, but `v` is not bound in the method's env. Any judgment that tries to resolve `v` — like `prove_is_mut` — fails.

## Problem 2: no block-scoped drops

Currently, the interpreter's `eval_block` does not drop variables when a block exits. All variables declared inside a block live until method exit. This means:

```dada
fn main() {
    {
        let temp = expensive_thing()
        use(temp.ref)
    }
    # temp is NOT dropped here — it lives until main() exits
    do_more_stuff()
}
```

Variables should be dropped at the end of the block that introduced them, following the same whole-place drop rules used at method exit.

## Design

### Fresh names for method calls

**Core idea:** Instead of starting each method with a fresh `base_env()`, start from the caller's env. Alpha-rename all variables in the method body to fresh names to avoid collisions with caller-scope variables.

When `call_method` is invoked:

1. **Start from caller's env** — pass the caller's `stack_frame.env` into `call_method` (currently it calls `self.base_env()`).

2. **Alpha-rename the method body** — clone the method's AST (body, input decls, output type) and rename all locally-declared variables to fresh names. Add a `call_depth: usize` field to `Interpreter` (separate from `indent`, which is for trace formatting). Increment on `call_method` entry, decrement on exit. A variable `x` at depth `N` becomes `Var::Id("_{N}_{x}")` — e.g., `self` → `_1_self`, `index` → `_2_index`. This keeps output readable while ensuring uniqueness across the call stack.

3. **Bind renamed parameters in the extended env** — push the renamed `_{N}_self` and renamed input variables into the caller's env. Since caller variables are still present, places like `v` in `mut[v]` resolve naturally.

4. **Execute the renamed body** — evaluate as before, but with the extended env.

5. **On return, discard the method's bindings** — the caller's env is restored (it was not mutated — `Env` is clone-based). The caller's stack frame is unaffected.

#### Variable renaming

**All** variables declared by the method are renamed, including `self`. The method body uses `Var::This` for `self`, which would collide with the caller's `Var::This` if the caller is also a method. After renaming, every reference to `self` in the method body — field accesses like `self.data`, types like `ref[self]`, permissions like `mut[self]` — uses the renamed `Var::Id("_{N}_self")` instead of `Var::This`. The receiver value is then bound to `_{N}_self` in the env (step 3 above), not to `Var::This`.

Specifically, the rename applies to:

- `Var::This` → `Var::Id("_{N}_self")`
- `Var::Id(x)` for each input parameter → `Var::Id("_{N}_{x}")`
- `Var::Id(x)` for each `let`-bound variable in the body → `Var::Id("_{N}_{x}")`

`Var::Return` is **not renamed**. It only appears in return type annotations (e.g., `ref[return]`) and is not bound in the interpreter's env during method execution.

The renaming applies throughout the method's AST: expressions, statements, type annotations, and any types embedded in the body (e.g., `ref[x]` becomes `ref[_{N}_x]`).

**Existing infrastructure:** The `InFlight` trait (`src/type_system/in_flight.rs`) already provides `with_places_transformed(Transform::Put(old_vars, new_places))` which substitutes variables inside types and permissions. This handles the type-level renaming. For the statement/expression level, we need a parallel traversal — `InFlight` currently covers `Ty`, `Perm`, `Place`, `Predicate`, etc., but not `Expr`, `Statement`, or `Block`.

#### Nested calls

This composes naturally. If `f` (depth 0) calls `g` (depth 1) calls `h` (depth 2):
- `h`'s env extends `g`'s, which extends `f`'s
- A type `mut[_1_v]` from `g`'s scope resolves in `h`'s env because the binding is inherited
- Depth-prefixed names ensure no collisions at any level

#### `Var::This` collisions

The caller's env may have `Var::This` bound (if the caller is itself a method). The method we're calling also has a `self`. We rename the callee's `self` to `Var::Id("_{N}_self")`, so there's no collision. The caller's `Var::This` (or `_0_self`, etc.) remains in the extended env, accessible for place resolution.

### Block-scoped drops

**Core idea:** When `eval_block` enters a block, snapshot the current set of variables. On block exit, drop (using whole-place rules) and remove any variables that were added during the block.

```
eval_block(stack_frame, block):
    vars_before = snapshot(stack_frame.variables)
    result = eval statements...
    new_vars = stack_frame.variables - vars_before
    for var in new_vars (reverse order):
        drop var using whole-place rules
        remove var from stack_frame.variables
        pop var from stack_frame.env
    return result
```

**Whole-place rules apply:** A variable is only dropped if it's whole (all accessible sub-places initialized). Partially-moved variables have their remaining initialized fields dropped individually, same as at method exit. The existing `drop_value` + `is_value_whole` logic handles this.

**Interaction with method exit:** With block-scoped drops, all `let`-bound locals are dropped by their enclosing blocks. However, method parameters (`self` and inputs) are bound by `call_method` *before* entering the body block, so they are not block-scoped and won't be cleaned up by `eval_block`. The method-exit cleanup loop in `call_method` should be reduced to dropping just the parameters.

**Return/break:** When a block exits early via `return` or `break`, the block-scoped variables still need to be dropped. The cleanup logic runs on ALL exit paths from the block.

**Drop order:** Variables are dropped in reverse declaration order (last declared → first dropped), matching Rust's semantics and general LIFO expectation.

**The final value:** The last expression in a block produces the block's result value. This value must NOT be dropped — it's the block's return value. Currently `eval_block` tracks this as `final_value`. The cleanup logic should skip the variable (if any) that holds the result, or more precisely: the result value has already been extracted from the block's scope by the time cleanup runs — it's returned as the block's `Outcome::Value`, not stored in a named variable.

Actually, looking at the current code more carefully: `let` statements return `unit`, and `Expr` statements produce values that become `final_value` — but those expression results are never bound to a variable in the block's scope. So block cleanup drops all `let`-bound variables, and the final expression's value passes through as the `Outcome`. No special case needed.

### Interaction between the two features

Block-scoped drops and fresh names are largely independent but share the same `eval_block` / `call_method` code paths:

- **Fresh names** change how `call_method` sets up the env (extend caller's instead of fresh)
- **Block-scoped drops** change how `eval_block` cleans up on exit

The method-exit cleanup in `call_method` becomes simpler (or goes away) once blocks handle their own drops:
- Method parameters (`self`, inputs) are bound before `eval_block` runs
- `eval_block` drops all `let`-bound locals in the body
- `call_method` only needs to drop the parameters themselves after `eval_block` returns

## Demonstrated bug: `vec_get_through_mut_ref`

The test `vec_get_through_mut_ref` (in `src/interpreter/tests/vector.rs`, currently `#[ignore]`) demonstrates the bug concretely. It calls `v.mut.get[mut[v]](0)` on a `Vec[Data]`. Inside `Vec.get`, `P` is substituted to `mut[v]`, and the method body uses `given_from[self]` as the permission for `array_give`. The resolution chain is:

1. `perm_to_operms(env, given_from[self])` → `prove_is_mut(env, Perm::Mv([self]))`
2. `env.place_ty(self)` → `mut[v] Vec[Data]` ✅ (self is in the method env)
3. `prove_is_mut(env, ApplyPerm(Mt([v]), Vec[Data]))` → `env.place_ty(v)` → ❌ **fails** (v is from caller scope)

Because `prove_is_mut` fails, `perm_to_operms` falls through to `Borrowed`. The `array_give` call produces a borrowed copy of the element instead of a MutRef into the array. Observable symptoms:

- Return value is `given_from[self] Data { x: 42 }` (a copied-out value) instead of `mut[v] Data` (a MutRef pointer into the array)
- Display of `data` inside the method shows `mut [v] <unexpected: RefCount(1)>` — the display code also fails to resolve `v`
- Mutations through the returned "reference" would not propagate back to the array

This test will be un-ignored once the fresh-names work lands.

## Alternatives considered

1. **Structural `prove_is_mut` rule** — add a rule that `Perm::Mt(_)` is always mut without resolving places. Rejected because it's semantically wrong: `mut[x]` where `x: shared Foo` should not be mut.

2. **Extract referenced variables into method env** — at call time, scan the receiver type for place references and bind just those in the method env. Simpler but fragile — misses places referenced in argument types, return types, or types computed during execution.

3. **Inline/rewrite semantics** — substitute the method body into the calling context directly. Clean semantically but a much larger architectural change to the interpreter.

## Implementation plan

**Agent workflow:** Complete ONE phase at a time. After each phase, commit the work, run `cargo test --all --all-targets` to confirm all tests pass, and **stop**. A human must review before the next phase begins.

### Phase 1: Block-scoped drops ✅ COMPLETE

Added block-scoped variable cleanup to `eval_block`. Independent of fresh names.

**Changes made:**
- Changed `Statement::Loop(Arc<Expr>)` to `Statement::Loop(Block)` in the grammar — loops now always take a block, ensuring block-scoped cleanup per iteration
- Changed `StackFrame.variables` from `Map<Var, Pointer>` to `Vec<(Var, Pointer)>` — preserves declaration order for reverse-order drops. Added `insert_variable()` and `get_variable()` helper methods.
- `eval_block` snapshots `stack_frame.variables.len()` on entry, calls `drop_block_scoped_vars()` on all exit paths (normal, break, return)
- `drop_block_scoped_vars()` pops variables in reverse declaration order, drops each using whole-place rules, and removes from `stack_frame.env`
- Method-exit cleanup loop in `call_method` retained as safety net (only parameters remain after block-scoped drops)
- No existing test snapshots required changes (drop timing was already correct for existing tests)
- `loop_body_value_is_freed` test updated: removed nested block since `Loop(Block)` now provides the outer block directly

**Tests added** (`src/interpreter/tests/block_scoped_drops.rs`):
- `block_scoped_drop` — variable dropped when inner block exits ✅
- `block_scoped_drop_order` — reverse declaration order (3, 2, 1) ✅
- `nested_blocks_drop_innermost_first` — inner drops before outer continues ✅
- `block_early_break_drops_locals` — break drops block-local vars ✅
- `loop_break_drops_locals` — vars drop per iteration and on break ✅

**Notes:**
- `block_early_return_drops_locals` skipped — `return` is not in KEYWORDS, so it parses as an identifier, causing ambiguity. The return path is covered by `Outcome::Return` propagation through `drop_block_scoped_vars`.
- `partial_move_in_block` skipped — existing `is_value_whole` logic handles this; no new test needed.
- No refcount timing issues observed — all existing tests pass unchanged.

### Phase 2: Extend `InFlight` to cover expressions and statements

Add `InFlight` implementations for `Expr`, `Statement`, `Block`, `MethodBody`, and any other AST nodes that contain variables. This is pure infrastructure — no behavioral change.

The rename in Phase 3 requires three steps, and this phase builds the infrastructure for all of them:

1. **Collect bound names** — walk the method body's AST to gather all locally-declared variable names. These are:
   - `Var::This` (always present)
   - Input parameter names from `MethodDeclBoundData.inputs` (known from the signature, no walk needed)
   - `let`-bound `ValueId`s from `Statement::Let(name, ...)` throughout the body (requires recursive walk into nested blocks, loop bodies, if-branches, etc.)

2. **Build the rename map** — from the collected names, construct the two parallel lists for `Transform::Put`: `[Var::This, Var::Id("x"), ...] → [Var::Id("_{N}_self"), Var::Id("_{N}_x"), ...]`

3. **Apply via `InFlight`** — the new `InFlight` impls use `Transform::Put` with the rename map to substitute variables throughout the AST

**Key detail for `Statement::Let`:** The `Let` variant stores its declared name as a raw `ValueId`, not as a `Var` or `Place`. The `InFlight` impl for `Statement` must rename this declaration-site `ValueId` in addition to transforming the types and expressions within the statement. This is unlike the `Place`/`Perm` impls where variable references are already wrapped in `Var`.

**`Arc<T>` handling:** Add a generic `impl<T: InFlight> InFlight for Arc<T>` that clones the inner value, transforms it, and wraps in a new `Arc`. Many `Expr` variants wrap sub-expressions in `Arc<Expr>`, so this keeps the per-variant impls simple.

**Testing:** Verify round-trip — apply `Transform::Put` with an identity mapping (each name maps to itself) and confirm the AST is unchanged.

### Phase 3: Alpha-rename method bodies in `call_method`

- Track `call_depth: usize` in the interpreter (increment on entry, decrement on exit)
- Change `call_method` to accept the caller's env. **Entry point:** `interpret()` calls `call_method` for `Main.main()` where there is no caller — pass `base_env()` as the caller env in this case.
- Before executing a method, alpha-rename its body (all locally-declared variables → `Var::Id("_{depth}_{name}")`)
- Extend the caller's env with the renamed bindings
- Execute the renamed body
- **Fix `display_value` after method exit:** The current code displays the return value using `base_env()`, which has no local variables. With fresh names, the return type contains renamed variables (e.g., `ref[_1_self]`). Use the caller's env (which has the renamed bindings) for the post-exit display instead.
- All existing tests should pass unchanged (behavior is identical, just variable names differ internally)
- **Update test snapshots** — trace output and displayed types will contain renamed variables (e.g., `_1_self` instead of `self`). Expect widespread snapshot diffs. Use `UPDATE_EXPECT=1 cargo test --all --all-targets` to regenerate.

### Phase 4: Replace `is_mut_ref_type` with `prove_is_mut`

- At each `is_mut_ref_type` call site, replace with `prove_is_mut(env, ty).is_proven()` (plus copy-type check if needed)
- Remove `is_mut_ref_type`
- Verify all tests pass — this confirms that `prove_is_mut` now succeeds for method-internal types because caller-scope places are resolvable
- **Note:** `perm_to_operms` (a type-system function) already calls `prove_is_mut` internally. It requires no changes — it will just work once the env contains caller-scope bindings (from Phase 3). The demonstrated bug in `vec_get_through_mut_ref` flows through `perm_to_operms`, so this is the path that gets fixed.

### Future: also propagate where-clause assumptions

The interpreter doesn't currently use where-clause assumptions at all. With the extended env, it *could* — e.g., if a method has `where P is mut`, the interpreter could consult that. This isn't needed for the `is_mut_ref_type` fix but would enable more type-system integration in the interpreter.

## FAQ

**Q: Can depth-prefixed names ever collide (e.g., recursive methods, same-depth calls)?**

No. `call_depth` increments on every `call_method` entry, so recursive calls get distinct prefixes (`_1_x`, `_2_x`, etc.). Same-depth calls are sequential — by the time the second call happens, the first call's variables have been cleaned up and removed from the env. No collision is possible.

**Q: Should `Var::Magic`, `Var::InFlight`, or `Var::Fresh` be renamed?**

No. These are synthetic variables that cannot appear in user code. They serve internal purposes (drop bodies, in-flight value tracking, type-checker fresh variables) and won't collide with depth-prefixed method variables.

**Q: Does `find_method` return a fresh AST clone that's safe to rename in place?**

Yes. `find_method` calls `binder.instantiate_with(method_parameters)` which substitutes parameters and produces an owned `MethodDeclBoundData`. The returned AST is already a fresh copy — no risk of mutating shared program data.
