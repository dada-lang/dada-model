# Var-pop normalization

## Problem

When a value's type references a variable that is about to go out of scope (be "popped"), the type becomes unresolvable. This happens in two places:

1. **Method return:** The return type may reference `self` or input parameters, which are popped when the method exits.
2. **Block exit:** The block's result type may reference `let`-bound variables that are popped when the block exits.

In most cases, referencing an out-of-scope variable in a type is an error — e.g., returning `ref[x] Data` where `x` is a local would be returning a dangling borrow. The liveness/scope checks catch this.

But `given_from[x]` is the exception. It means "ownership derived from `x`." The value isn't borrowing `x` — it received ownership from `x`. The permission of the result depends on what `x`'s permission was, but `x` itself doesn't need to stay live.

Currently, neither the type system nor the interpreter normalizes `given_from[x]` when `x` goes out of scope. Both work around this by accident or by workaround:

- **Type system:** `Var::This` in the return type accidentally resolves to the *caller's* `self` (a different variable that happens to share the name). Type proofs succeed for the wrong reason.
- **Interpreter:** After the fresh-names work (Phase 3), method parameter type bindings are injected into the caller's env so proofs can resolve the renamed variables. This works but leaks method-internal names into the caller's scope.

## Demonstrated bugs

### Type system: `Var::This` collision in return types

In `src/type_system/expressions.rs`, the "call" rule:

```
(resolve_method(env, receiver_ty, method_name, parameters) => (this_input_ty, inputs, output, predicates))
...
(let (this_input_ty, input_tys) = (this_input_ty.clone(), input_tys.clone()).with_this_stored_to(this_var))
...
(let env = env.pop_fresh_variables(input_temps))
(let output = output.with_place_in_flight(Var::Return))
```

`with_this_stored_to(this_var)` is applied to the *input* types but NOT to `output`. So the return type still has `Var::This` references. After `pop_fresh_variables` removes `this_var`, the output type's `Var::This` resolves to the *caller's* `self` — a completely different variable.

Example: if `Vec.get` returns `given_from[self] Data` and the caller is `Main.main`, then `self` in the return type resolves to `Main` (the caller's self), not to the `Vec` instance. Type proofs happen to succeed because `Main` is owned, but the resolution is semantically wrong.

### Interpreter: type binding injection workaround

After the fresh-names work, the interpreter alpha-renames method variables (`self` → `_N_self`). The return type `given_from[_N_self] Data` references a variable that only existed in the method's scope. The workaround: inject `_N_self`'s type binding into the caller's env after the method returns. This lets proofs resolve but means method-internal names leak into the caller's scope indefinitely.

## Design sketch

### Normalization rule

When a variable `x` is popped from scope and a type references `given_from[x]`:

1. Look up `x`'s type in the env (before popping)
2. Determine the permission of `x`'s type
3. Replace `given_from[x]` with the resolved permission

Examples:
- `x: shared Vec[Data]` → `given_from[x]` normalizes to `shared` (giving from shared produces shared)
- `x: given Vec[Data]` → `given_from[x]` normalizes to `given` (giving from owned produces owned)
- `x: mut[v] Vec[Data]` → `given_from[x]` normalizes to `mut[v]` (giving from mut produces mut — the borrow chain is preserved, but `x` itself is removed)

### Where to apply

- **Method return:** Before the return type escapes to the caller, normalize any `given_from[param]` references for all parameters being popped.
- **Block exit:** Before the block's result type escapes to the enclosing scope, normalize any `given_from[local]` references for all locals being popped.

### Interaction with `given_from[x.field]`

`given_from` can reference places with projections, e.g., `given_from[self.data]`. Normalization needs to handle this: look up the type of the full place `self.data`, determine its permission, and substitute.

### Recursive normalization

The resolved permission might itself contain place references that need normalizing. E.g., `given_from[x]` where `x: mut[y] T` normalizes to `mut[y]` — but if `y` is also being popped, `mut[y]` needs further normalization. This should converge since the chain of place references is finite.

## Test cases to write

### Type system tests

1. **Method returns `given_from[self] T` called from another method** — currently passes by accident (Var::This collision). After fix, should still pass but with correct resolution.

2. **Method returns `given_from[self] T` where caller's self has a DIFFERENT owned-ness** — would expose the collision if the caller's self were not owned. Need to construct a case where the caller's self is e.g. `ref[x] Foo` (not owned) but the callee's self is `given Foo` (owned). The return type should be treated as owned (from callee's self) but the collision would make it non-owned (from caller's self).

3. **Block returns value with `given_from[local]`** — the local goes out of scope when the block exits. The type should be normalized.

### Interpreter tests

1. Corresponding runtime tests for the above, verifying the interpreter produces correct values and permissions.

## Relationship to current workarounds

The interpreter's type binding injection (from the fresh-names Phase 3) is a temporary workaround. Once var-pop normalization is implemented:

- The type system will normalize return types at call boundaries and block exits
- The interpreter can do the same normalization, removing the need for type binding injection
- Method-internal names will no longer leak into the caller's scope
