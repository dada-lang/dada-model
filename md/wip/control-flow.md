# Non-Straightline Control Flow

> **Status: Design in progress.** We are still working out the right approach. Nothing here is final.

## Problem

The type checker threads `Env` and `LivePlaces` linearly through judgments, as if all code were straight-line. This breaks down for every form of non-straightline control flow:

### If/else: branches treated sequentially

```rust
(type_expr_as(env, ..., &**cond, TypeName::Bool) => env)
(type_expr_as(env, ..., &**if_true, Ty::unit()) => env)   // env from cond
(type_expr_as(env, ..., &**if_false, Ty::unit()) => env)   // env from if_true!
```

Two bugs:
1. **The false branch sees mutations from the true branch.** The `env` output from checking `if_true` (with in-flight permission rewrites) is fed into `if_false`, as if both branches execute sequentially.
2. **The output env is from the last branch only.** After the if/else, the env should reflect a *join* of both branches — what's true on both paths. Currently it just takes whatever fell out of the false branch.

### Loop: no back-edge, env leaks

```rust
Statement::Loop(block) => block.adjust_live_vars(live),
```

1. **Liveness doesn't account for the back-edge.** A single pass through the body misses that variables used at the start are live at the end (next iteration). This is under-approximate — potentially unsound, since it could allow moves of things needed in the next iteration.
2. **The loop type rule discards the body env** (correctly, as implemented), but the liveness fed into the body doesn't reflect the repeating nature of the loop.

### Break: no loop context

```rust
Statement::Break => live,   // just passes through
```

1. **Liveness from dead code after `break` propagates backwards.** Over-approximate (conservative), but imprecise.
2. **Break doesn't know what's live after the enclosing loop.** The `adjust_live_vars` trait has no loop context, so break can't contribute the right liveness.

## Root cause

All three issues stem from the same thing: the type checker assumes linear control flow. `Env` is threaded A → B → C, but control flow is actually:

- **If/else**: fork into two paths, then join
- **Loop**: cycle (body feeds back into itself)
- **Break**: non-local exit to a surrounding scope

## Observations

### Why `Env` is threaded at all

The `Env` carries `local_variables: Map<Var, Ty>`, and types contain permission places. The env is threaded as output because **in-flight permission tracking** rewrites those places as values move:

- `with_in_flight_stored_to` — value lands in a variable, `Var::InFlight` → actual place
- `with_var_stored_to` — value moves between variables, permissions updated
- `push_local_variable` / `pop_fresh_variable` — variables enter/leave scope

The `universe`, `in_scope_vars`, `assumptions`, and `program` fields are never modified through the output path.

### Loop context in `Env`

Since `Env` is already threaded everywhere, it's a natural place to carry loop context. For example, a field like `break_live: Option<LivePlaces>` — `None` outside loops, `Some(live_after_loop)` inside. The `loop` rule sets it; the `break` rule reads it.

## Design space (under discussion)

Things we need to figure out:

- **Env forking/joining for if/else**: How to fork env before branches and join after? What does "join" mean for permission places that diverged?
- **Loop fixed-point for liveness**: Iterate `body_live_after = live_after_loop ∪ block.adjust_live_vars(body_live_after)` until stable? Do this in `adjust_live_vars`, the type rule, or both?
- **Loop fixed-point for env**: Does the env need a fixed-point too (permissions could change across iterations)? Or is it enough to check the body once with conservative assumptions?
- **Break context**: Add `break_live` to `Env`? Or restructure `adjust_live_vars` to carry loop context?
- **Interaction between fixes**: Can we address these incrementally, or do they need to be solved together?

## Existing tests

Three loop tests were changed from `type: error, interpret: ok` to `type: ok, interpret: ok` with the initial loop/break rules:
- `loop_body_value_is_freed`
- `block_early_break_drops_locals`
- `loop_break_drops_locals`

These pass with the current (incomplete) implementation but may need updating as we improve correctness.

New tests to write once the design settles:
- Variable used across loop iterations (back-edge liveness)
- Move in loop body with reassignment (live across back-edge prevents premature move)
- If/else where one branch moves a variable (join must reflect the move)
- Break inside nested blocks within a loop
- Dead code after break
