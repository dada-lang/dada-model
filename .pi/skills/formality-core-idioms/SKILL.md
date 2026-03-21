---
name: formality-core-idioms
description: Idiomatic patterns for writing code with formality-core (a-mir-formality). Covers generated constructors, Upcast/UpcastFrom coercions, judgment_fn! macro patterns, #[term] enum/struct conventions, and common pitfalls. Use when writing or reviewing judgment functions, type definitions, or parser-related code in projects built on formality-core.
---

# Idiomatic formality-core

This skill covers patterns and anti-patterns when writing code with [formality-core](https://rust-lang.github.io/a-mir-formality/formality_core.html). Following these idioms produces cleaner, more concise code and avoids subtle bugs.

## Generated constructors from `#[term]`

The `#[term]` macro generates constructor methods on every type it annotates.

### Structs get `::new(...)`

```rust
#[term($name $[?parameters])]
pub struct NamedTy {
    pub name: TypeName,
    pub parameters: Parameters,
}
```

Generates: `NamedTy::new(name, parameters)` where each parameter accepts `impl Upcast<FieldType>`.

### Enums get `::snake_case_variant(...)`

```rust
#[term]
pub enum Perm {
    #[grammar(given_from $[v0])]
    Mv(Set<Place>),
    Given,
    Shared,
    #[grammar(ref $[?v0])]
    Rf(Set<Place>),
    #[grammar(mut $[v0])]
    Mt(Set<Place>),
    #[variable(Kind::Perm)]
    Var(Variable),
    Apply(Arc<Perm>, Arc<Perm>),
}
```

Generates lowercase snake_case methods. Rust keywords get a trailing `_`:

| Variant | Generated method |
|---------|-----------------|
| `Mv(Set<Place>)` | `Perm::mv(places)` |
| `Given` | *(no method — zero fields)* |
| `Shared` | *(no method — zero fields)* |
| `Rf(Set<Place>)` | `Perm::rf(places)` |
| `Mt(Set<Place>)` | `Perm::mt(places)` |
| `Var(Variable)` | `Perm::var(v)` |
| `Apply(Arc<Perm>, Arc<Perm>)` | `Perm::apply(p1, p2)` |

Zero-field variants (like `Given`, `Shared`) get **no** generated constructor — use the enum literal `Perm::Given` directly.

#### Rule: always prefer generated constructors

```rust
// ✅ Good — generated constructor, accepts impl Upcast
Perm::var(perm_var)
Perm::rf(set![place])
NamedTy::new(name, substitution)
Predicate::parameter(ParameterPredicate::Copy, perm_var)

// ❌ Bad — manual construction, requires explicit conversion
Perm::Var(perm_var.upcast())
Perm::Var(Variable::from(perm_var.clone()))
Perm::Rf(set![place.clone()])
```

The generated constructors accept `impl Upcast<T>` for every field, so they handle conversions (e.g., `UniversalVar` → `Variable` → `Perm::Var`) and cloning automatically. You never need to manually `.upcast()`, `.into()`, or `.clone()` when calling a generated constructor.

## Upcast coercions: avoiding explicit clones

The `Upcast`/`UpcastFrom` system provides automatic coercions. The key blanket impl:

```rust
impl<T: Clone, U> UpcastFrom<&T> for U where U: UpcastFrom<T> { ... }
```

This means: **anywhere `impl Upcast<T>` is expected, you can pass `&T` and it will clone for you.** This eliminates most explicit `.clone()` calls.

### Where this applies

1. **Generated constructors** — all parameters accept `impl Upcast<FieldType>`
2. **`judgment_fn!` parameters** — the function signature is `fn f(x: impl Upcast<T>)`
3. **`Env` methods** — `push_local_variable`, `add_assumptions`, etc. accept `impl Upcast<T>`

### Common coercion chains

| Source | Target | How |
|--------|--------|-----|
| `&T` | `T` | auto-clone via `UpcastFrom<&T>` |
| `UniversalVar` | `Variable` | `UpcastFrom` |
| `UniversalVar` | `Parameter` | via `Variable` → `Parameter` |
| `NamedTy` | `Ty` | `#[cast]` on `Ty::NamedTy` variant |
| `Place` | via `Var` | `UpcastFrom<Var> for Place` |
| `Vec<T>` | `Vec<U>` | element-wise upcast |
| `&[T]` | `Vec<U>` | element-wise upcast |

### Examples

```rust
// ✅ Good — pass &reference, upcast handles cloning
let env = env.push_local_variable(Var::This, &class_ty)?;
Predicate::parameter(ParameterPredicate::Copy, &perm_var)

// ❌ Bad — unnecessary explicit clone
let env = env.push_local_variable(Var::This, class_ty.clone())?;
Predicate::parameter(ParameterPredicate::Copy, perm_var.clone())
```

**Exception:** When the value is already owned and you're done with it, just pass it directly — no `&` needed:

```rust
// ✅ Good — class_ty is owned and consumed here
let env = env.push_local_variable(Var::This, class_ty)?;
```

## `judgment_fn!` patterns

### Parameters are owned inside the body

The macro expands `fn f(x: impl Upcast<T>)` and immediately does `let x: T = Upcast::upcast(x)`. Inside the rule body, `x` is an **owned `T`**. However, within pattern-matched destructuring, fields from a matched struct/enum are **references** (standard Rust match ergonomics).

```rust
judgment_fn! {
    fn check(env: Env, decl: ClassDecl) => () {
        (
            // `decl` is owned ClassDecl
            // After destructuring, `name` is `&ValueId`, `binder` is `&Binder<...>`
            (let ClassDecl { name, binder, .. } = decl)
            // But generated constructors accept `impl Upcast<T>`,
            // which includes `&T`, so this just works:
            (let class_ty = NamedTy::new(name, substitution))  // ✅ name is &ValueId, auto-cloned
            ...
        )
    }
}
```

### Pattern matching in conclusions for dispatch

Use pattern matching in the conclusion to dispatch on variants — cleaner than `if` guards:

```rust
// ✅ Good — pattern match directly
(
    (let env = env.push_local_variable(Var::This, class_ty)?)
    ...
    ----------------------------------- ("given_class_drop")
    (check_drop_body(class_ty, ClassPredicate::Given, env, body) => ())
)

(
    ...
    ----------------------------------- ("share_class_drop")
    (check_drop_body(class_ty, ClassPredicate::Share | ClassPredicate::Shared, env, body) => ())
)

// ❌ Avoid — if-guard when pattern match works
(
    (if *class_predicate == ClassPredicate::Given)
    ...
    ----------------------------------- ("given_class_drop")
    (check_drop_body(class_ty, class_predicate, env, body) => ())
)
```

### Cut points with `!`

Place `!` after a condition to mark a **match commit point**. Rules that fail before the cut are excluded from error reports. Use cuts on guard conditions that definitively select or reject a rule:

```rust
// ✅ Good — cut prevents "empty_drop failed" noise in error messages
(
    (if drop_body.block.statements.is_empty())!
    ----------------------------------- ("empty_drop")
    (check_drop_body(_class_ty, _class_predicate, _env, drop_body) => ())
)
```

Without the `!`, if the empty check passes but a later rule fails, error reports would unhelpfully include "empty_drop failed because condition was false" for non-empty bodies.

### `Arc<T>` gotcha

Fields declared as `Arc<T>` become `&Arc<T>` when destructured (standard Rust). Calling `.clone()` gives you `Arc<T>`, **not `T`**. Use `T::clone(x)` to get a `T` via deref coercion:

```rust
// Inside a judgment rule where `expr` is `&Arc<Expr>`:
(let owned_expr: Expr = Expr::clone(expr))  // ✅ Gets Expr, not Arc<Expr>
(let arc_copy: Arc<Expr> = expr.clone())     // Gets Arc<Expr> — usually not what you want
```

### `for_all` vs `in`

- `(x in collection)` — **existential**: there exists some `x` in `collection` that satisfies the remaining conditions
- `(for_all(x in collection) (condition))` — **universal**: all `x` in `collection` must satisfy `condition`

```rust
// Check ALL fields
(for_all(field in fields)
    (check_field(env, field) => ()))

// Find SOME method matching the name
(MethodDecl { name: _, binder } in methods.into_iter().filter(|m| m.name == *method_name))
```

## Parser / grammar conventions

### Kind keywords are lowercase

formality-core parses `Kind` variants as their lowercase names. For a `Kind` enum with `Ty` and `Perm` variants, the parser keywords are `ty` and `perm`:

```rust
// ✅ Correct in test strings / parsed programs
"class Wrapper[ty T] { ... }"
"class Foo[perm P, ty T] { ... }"

// ❌ Wrong — "type" is not a keyword
"class Wrapper[type T] { ... }"
```

### KEYWORDS vs grammar keywords

Words in the `KEYWORDS` list in `declare_language!` are **globally reserved** — they can never be used as identifiers anywhere. Grammar keywords (`#[grammar(x)]` on enum variants) work without being in KEYWORDS — they're only recognized in the specific parsing context.

**Only add to KEYWORDS when you want to block identifier use.** Don't add a word to KEYWORDS just because it appears in a `#[grammar(...)]` annotation.

### Prefix ambiguity

If one variant's keyword is a prefix of another's in the same enum (e.g., `given` vs `given_from[...]`), the parser silently matches the shorter one. Use distinct keywords to avoid this.

### `$?` for optional fields

`$?field` in a grammar annotation makes the field optional. The field type must implement `Default`. When the field is absent in the input, the `Default` value is used:

```rust
#[term($:where $,predicates { $*fields $*methods $?drop_body })]
pub struct ClassDeclBoundData {
    pub predicates: Vec<Predicate>,
    pub fields: Vec<FieldDecl>,
    pub methods: Vec<MethodDecl>,
    pub drop_body: DropBody,  // Default::default() when omitted
}
```

## Summary of rules

1. **Use generated constructors** (`Perm::var(x)` not `Perm::Var(x.upcast())`)
2. **Pass references** where `impl Upcast<T>` is expected — the framework clones for you
3. **Pattern match** in judgment conclusions instead of `if` guards
4. **Use `!` cuts** on guard conditions to reduce error noise
5. **Use `T::clone(x)`** for `Arc<T>` fields, not `.clone()`
6. **Use `ty`/`perm`** as kind keywords in parsed strings, not `type`/`perm`
7. **Don't add to KEYWORDS** unless you need to reserve the word globally
