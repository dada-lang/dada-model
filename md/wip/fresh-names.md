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

### Phase 2: Extend `InFlight` to cover expressions and statements ✅ COMPLETE

Added `InFlight` implementations for `Expr`, `Statement`, `Block`, `MethodBody`, `DropBody`, `MethodDeclBoundData`, `Ascription`, `PlaceExpr`, and `Arc<T>`. Also added `collect_bound_vars()` and `alpha_rename_method()` functions for Phase 3.

**Changes made:**
- `InFlight for Arc<T>` — generic impl that clones inner, transforms, re-wraps
- `InFlight for Block` — transforms statements
- `InFlight for Statement` — handles all variants including `Let` (renames `ValueId` at declaration site via `rename_value_id`)
- `InFlight for Ascription` — transforms type annotation
- `InFlight for Expr` — handles all variants (Block, Integer, BinaryOp, Place, Share, Tuple, Call, New, Clear, If, SizeOf, Array*, IsLastRef, Panic)
- `InFlight for PlaceExpr` — transforms place, preserves access
- `InFlight for MethodBody` — Trusted passthrough, Block transforms
- `InFlight for DropBody` — transforms block
- `InFlight for MethodDeclBoundData` — transforms this, inputs, output, predicates, body
- `rename_value_id()` helper — renames raw `ValueId` declaration sites via `Transform::Put`
- `collect_bound_vars()` — walks method AST to collect `Var::This`, input params, and all `let`-bound names
- `alpha_rename_method()` — builds rename map and applies `Transform::Put` to produce renamed method + mapping

### Phase 3: Alpha-rename method bodies in `call_method` ✅ COMPLETE

Alpha-renamed method bodies use depth-prefixed variables and execute in the caller's extended env.

**Changes made:**
- Added `next_call_id: usize` to `Interpreter` — monotonically increasing counter (not stack-based depth). Each method call gets a globally unique ID, preventing name collisions even for sequential calls at the same stack depth.
- `call_method` now takes `&mut StackFrame` (the caller's) instead of `&Env`. This allows injecting the method's type bindings into the caller's env after the method returns.
- Before execution, method body is alpha-renamed via `alpha_rename_method(method_data, call_id)`. All locally-declared variables get `_{id}_` prefixed names (e.g., `self` → `_1_self`, `x` → `_1_x`).
- Method executes in a NEW `StackFrame` whose env extends the caller's env with the renamed bindings. Caller-scope places (e.g., `v` in `mut[v]`) remain resolvable.
- **Type binding injection:** After the method returns, its parameter type bindings (`_N_self: T`, `_N_input: T`) are injected into the caller's env via `push_local_variable`. This is critical: the return type may reference method-scope variables (e.g., `given_from[_N_self]`), and the caller needs these bindings for type proofs (`is_owned`, `is_copy`, etc.). Without this, an assertion failure occurs when the caller tries to give/ref the returned value.
- `display_value` after method exit uses the caller's env (which now has the method's bindings).
- `interpret()` creates a root `StackFrame` for the `Main.main()` call.
- Added `Env::has_local_variable()` helper.
- All 553 tests pass. Widespread snapshot diffs updated via `UPDATE_EXPECT=1`.

**Design insight discovered during implementation:** In the old code, return types like `given_from[self]` accidentally resolved through `Var::This` collision — the caller's `self` happened to satisfy the proof even though it referred to a different object. Alpha-renaming exposed this: `given_from[_N_self]` correctly doesn't exist in the caller's scope. The fix (injecting type bindings) is semantically sound because the renamed names are globally unique and the type bindings accurately describe the method parameters' types. However, type binding injection is a **temporary workaround** — the proper fix is var-pop normalization (see `md/wip/var-pop-normalization.md`). The same `Var::This` collision bug exists in the type checker's "call" rule in `src/type_system/expressions.rs`, where `output` is never transformed via `with_this_stored_to`.

**Why monotonic IDs, not stack-based depth:** Stack-based depth (increment on entry, decrement on exit) would reuse the same prefix for sequential calls. The second call would try to `push_local_variable` a name that already exists (from the first call's type binding injection), triggering a shadowing error. Monotonic IDs avoid this entirely.

### Phase 4: Replace `is_mut_ref_type` with `prove_is_mut`

- At each `is_mut_ref_type` call site, replace with `prove_is_mut(env, ty).is_proven()` (plus copy-type check if needed)
- Remove `is_mut_ref_type`
- Verify all tests pass — this confirms that `prove_is_mut` now succeeds for method-internal types because caller-scope places are resolvable
- **Note:** `perm_to_operms` (a type-system function) already calls `prove_is_mut` internally. It requires no changes — it will just work once the env contains caller-scope bindings (from Phase 3). The demonstrated bug in `vec_get_through_mut_ref` flows through `perm_to_operms`, so this is the path that gets fixed.

### Future: var-pop normalization (see `md/wip/var-pop-normalization.md`)

The type binding injection in Phase 3 is a temporary workaround. When a method returns a type like `given_from[_N_self] Data`, the proper fix is to **normalize** that permission by resolving `_N_self`'s type and collapsing to the concrete permission (e.g., `shared`, `given`, `mut[v]`). This normalization should happen whenever variables are popped from scope — at method returns and block exits. Both the type system and interpreter need this fix. The same underlying bug (unresolved place references in escaped types) exists in the type checker's "call" rule, where it manifests as an accidental `Var::This` collision. See `md/wip/var-pop-normalization.md` for the full design.

### Future: also propagate where-clause assumptions

The interpreter doesn't currently use where-clause assumptions at all. With the extended env, it *could* — e.g., if a method has `where P is mut`, the interpreter could consult that. This isn't needed for the `is_mut_ref_type` fix but would enable more type-system integration in the interpreter.

## FAQ

**Q: Can ID-prefixed names ever collide (e.g., recursive methods, same-depth calls)?**

No. `next_call_id` is a monotonically increasing counter — each method invocation gets a unique ID. Recursive calls get distinct prefixes (`_1_x`, `_2_x`, etc.), and sequential calls at the same stack depth also get distinct prefixes (`_2_x`, `_3_x`). No collision is possible, even with type binding injection into the caller's env.

**Q: Should `Var::Magic`, `Var::InFlight`, or `Var::Fresh` be renamed?**

No. These are synthetic variables that cannot appear in user code. They serve internal purposes (drop bodies, in-flight value tracking, type-checker fresh variables) and won't collide with depth-prefixed method variables.

**Q: Does `find_method` return a fresh AST clone that's safe to rename in place?**

Yes. `find_method` calls `binder.instantiate_with(method_parameters)` which substitutes parameters and produces an owned `MethodDeclBoundData`. The returned AST is already a fresh copy — no risk of mutating shared program data.
