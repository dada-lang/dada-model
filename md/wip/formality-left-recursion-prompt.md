# Formality-core: left-recursion seed produces right-associative bias

## Context

I'm updating [dada-model](https://github.com/nikomatsakis/dada-model) to the latest formality-core commit (`1f47788e`). The new parser changed `ParseResult` from returning a single `SuccessfulParse` to a `Set<SuccessfulParse>`, propagating ambiguity upward instead of picking one result per nonterminal.

This exposed a grammar ambiguity in dada-model that the old parser silently resolved. But investigating it revealed what appears to be an unintentional bias in the left-recursion machinery itself.

## The grammar

Dada has (simplified):

```rust
#[term]
pub enum Perm {
    #[grammar(given)]
    Given,
    #[grammar(shared)]
    Shared,
    #[grammar(mut $[v0])]
    Mt(Set<Place>),
    // ... other leaf variants ...

    #[grammar($v0 $v1)]
    Apply(Arc<Perm>, Arc<Perm>),  // perm composition
}

#[term]
pub enum Ty {
    #[cast]
    NamedTy(NamedTy),
    #[variable(Kind::Ty)]
    Var(Variable),

    #[grammar($v0 $v1)]
    ApplyPerm(Perm, Arc<Ty>),  // apply perm to type
}
```

## The bug/bias

Parsing `given given given` as a `Perm` produces **only** the right-associative interpretation:

```
Apply(Given, Apply(Given, Given))
```

The left-associative `Apply(Apply(Given, Given), Given)` is never generated.

### Why

The left-recursion fixed-point iteration in `left_recursion.rs` stores only the **single longest** parse as the seed for reuse:

```rust
let best_value = all_values.iter().min_by_key(|s| s.text.len()).unwrap();
with_top!(|top| {
    top.value = Some(erase_type(best_value));
});
```

Tracing through `given given given`:

- **Round 0**: No seed → only `Given` succeeds (consuming `"given"`, leaving `" given given"`).
- **Round 1**: Seed = `Given`. `Apply`'s left-recursive `$v0` returns the seed. `$v1` is a fresh parse that independently produces `Given` and `Apply(Given, Given)`. Results: `Given`, `Apply(Given, Given)` (remainder `" given"`), `Apply(Given, Apply(Given, Given))` (remainder `""`).
- **Round 2**: Seed = `Apply(Given, Apply(Given, Given))` (the longest — consumed everything). `Apply`'s `$v0` returns this, but `$v1` has no text left → no new values → fixed point.

The intermediate result `Apply(Given, Given)` is never used as a seed, so the left-associative parse `Apply(Apply(Given, Given), Given)` is never produced.

## The cross-type ambiguity this causes

When parsing `mut[pair] Q Data` as a `Ty` (where `Q` is an in-scope perm variable), two interpretations exist:

1. `ApplyPerm(Mt({pair}), ApplyPerm(Var(Q), NamedTy(Data)))` — perm is just `mut[pair]`
2. `ApplyPerm(Apply(Mt({pair}), Var(Q)), NamedTy(Data))` — perm is `mut[pair] Q`

Both are structurally different, so `core_term_with` panics with "ambiguous parse." In dada-model these are semantically equivalent (Apply is just curried perm composition), but the parser doesn't know that.

In pure-Perm contexts (e.g., inside `or(shared mut[d1], shared mut[d2])`), commas delimit the items, so there's no ambiguity — `Apply(Shared, Mt({d1}))` is the only parse that consumes everything before the comma.

## Discussion of possible fixes

### Option A: Generate all parses, disambiguate after

Instead of using a single seed, use ALL accumulated values as seeds for left-recursion. This would produce both left- and right-associative parses. Then add a post-parse disambiguation mechanism:

- **Normalization**: Let types provide a canonicalization function. Two parses that normalize to the same value are equivalent. (Dada already has `LeafPerms` / `push_leaves` / `from_leaves` that flatten `Apply` chains.)
- **Preference annotations**: `#[precedence]` / associativity applied as a filter on results rather than a parse-time restriction.

This cleanly separates the two concerns the current machinery conflates:
1. **Termination** — preventing infinite recursion (the fixed-point iteration handles this)
2. **Disambiguation** — choosing among valid parses (done after-the-fact)

Potentially slower (more parses generated), but more principled.

### Option B: Fix the single-seed to iterate over all seeds

Keep the current architecture but when multiple accumulated values exist, try each as a seed. This would produce `Apply(Apply(Given, Given), Given)` alongside `Apply(Given, Apply(Given, Given))`. Combined with the existing `core_term_with` dedup (which already removes structurally equal results), this might "just work" for cases where both parses exist but only one consumes all input.

Doesn't help with the cross-type ambiguity though, since both interpretations consume all input.

### Option C: Keep current behavior, add normalization at `core_term_with`

Leave the left-recursion machinery as-is. Add a trait like `ParseNormalize` that types can implement. `core_term_with` normalizes all values before dedup. This is the most surgical fix.

## Aside: `each_comma_nonterminal` / `each_delimited_nonterminal` lost collection genericity

Separate from the left-recursion issue, the new continuation-based parser methods `each_comma_nonterminal` and `each_delimited_nonterminal` hardcode `Vec<T>` as the collection type passed to the continuation. The old (non-continuation) API used `C: FromIterator<T>`, which allowed parsing into `Set<T>`, `Vec<T>`, etc.

This breaks dada-model's `Perm` enum, which uses `Set<Place>` fields with `$[v0]` grammar (e.g., `Mv(Set<Place>)` with `#[grammar(given $[v0])]`). The macro generates `|v0: Set<Place>, __p|` as the closure parameter, but the method passes `Vec<Place>`.

I have a fix on a local branch (`fix/collection-parse` in my a-mir-formality checkout) that adds a generic `C: FromIterator<T> + Debug` parameter to both methods, keeping `Vec<T>` as the internal accumulator and converting via `into_iter().collect()` when calling the user's continuation. All existing formality tests pass.

## What to investigate

1. If we change the seed to iterate over all accumulated values, what breaks in the formality-rust test suite? Does the `Expr` precedence/associativity machinery still work correctly, or does it rely on the single-seed bias?

2. The existing `#[precedence(N, left/right/none)]` annotations interact with the left-recursion machinery via `precedence_valid` checks and `min_precedence_level`. If we generate all parses and disambiguate after, can these annotations move to post-parse filtering cleanly?

3. Is the `Both` associativity (the default) intentionally permissive, or is it just papering over the single-seed issue?
