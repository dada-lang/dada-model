# Status note

This effort is mildly blocked on a related surface-syntax question: we also need to decide how permission and other parameters are written and resolved at **method call sites**, not just in declarations. That turns out to be a non-trivial part of the design/elaboration story, so the overall project is somewhat larger in scope than this doc originally assumed. It is not fully blocked, but it is not quite as self-contained as it first appeared.

# Features in scope

- `!` as postfix sugar for `mut` (in permissions and place expressions)
- Place expressions default to `.ref` when no access mode is given
- `.share` applied to a place expands to `.give.share`
- Implicit/default permissions on function parameters, while preserving bare field/return types
- Inline type and permission parameters (including the `any` keyword)

# Goal

Match Dada's planned surface syntax, taking advantage of the new elaborator and improvements in formality's parsing capabilities.

# Motivation

The goal is to modify our examples to follow Dada's surface syntax. There are a number of places we deviate presently.

## mut => `!`

We plan to offer a postfix `!` syntax as a sugar for `mut` in permissions and in place expressions. Note that this claims postfix `!` as a place/permission operator: it cannot later be reused for negation, unwrap, macros, or any other meaning without parser surgery. Recording the decision here.

```
class Foo {
    bar: String
}

let foo: Foo

let x: foo.bar! String = foo.bar!
# sugar for `let x: mut[foo.bar] String = foo.bar.mut`
```

## place expr default to `ref`

The default for a place expression is `ref`:

```
class Foo {
    bar: String
}

let foo: Foo

let x: foo.bar String = foo.bar
# sugar for `let x: ref[foo.bar] String = foo.bar.ref`
```

This default applies to the **whole place expression**, not to each prefix. So:

```dada
foo.bar.baz
```

elaborates to:

```dada
foo.bar.baz.ref
```

not to something like `foo.ref.bar.ref.baz.ref`.

## share applied to a place expands to `.give.share`

The share operator applied to a place "gives" the place and then shares the result:

```
class Foo {
    bar: String;
}

let foo: Foo;

let x: shared String = foo.bar.share;
# sugar for `let x: shared String = foo.bar.give.share`
```

This rewrite is **purely syntactic**: the elaborator always rewrites `place.share` to `place.give.share` without consulting types. If `.give` is not legal on that place (for example, because the place is reached through a `ref`), the type checker will report a `.give` error on a `.give` the user never wrote. The fix is on the diagnostic side — when reporting an error on a `.give` that came from `.share` desugaring, the elaborator should attach provenance so the message can say "this `.give` was introduced by `.share` on `<place>`".

## rename `given_from` to `given`

We currently use the `given_from` keyword for the place-based form. The intended end state is to remove that spelling entirely and use `given` for both forms throughout the language:

- `given T` — the concrete owned-unique permission.
- `given[places] T` — a symbolic permission representing ownership transferred out of those specific places.

The parser disambiguates by looking ahead for `[`.

This is not just a surface sugar. The old `given_from` spelling should be removed from the language rather than retained as a legacy alias.

## implicit permissions on function parameters

Every function parameter with no explicit permission gets a **fresh, unconstrained permission variable**, hoisted to the enclosing fn/method binder. `self` is not special — the same rule applies to every parameter. Each omitted-perm parameter gets its *own* fresh variable, so they are independent.

The `any` keyword is **equivalent to omitting the permission**: it introduces a fresh, unconstrained perm var. It exists as an *explicit* form for readability and to catch accidental omissions in code review.

`any` is legal in function/method parameter positions and inside type arguments (e.g. `Vec[any]`, `Iterator[any, any]`). It is **not** legal as a bare permission on a return type — `fn f(self) -> any String` is an error. Since `any` is also shorthand for anonymous inline parameters, it is likewise rejected anywhere inline params are rejected (for example, inside return types).

Bare field types and bare return types are preserved exactly as written. In today's core language those plain forms are the existing owned form (for example `-> String` remains `-> String`, rather than being elaborated to an explicit `given String`). Parameters are different: an omitted permission on a parameter introduces a fresh perm variable.

Why fully-unconstrained rather than e.g. defaulting to `is ref`? `perm P` and `perm P where P is ref` admit exactly the same operations on the parameter (in both cases the body must assume the value might be a reference), but the unconstrained form lets *callers* pass anything — owned, shared, mut, ref. Defaulting to fully unconstrained is therefore strictly more ergonomic at call sites with no cost in the body.

### `!` on a parameter binder

Postfix `!` on a parameter binder is sugar for adding an `is mut` predicate to that parameter's (implicit) permission variable. It **composes** with the implicit-perm rule rather than replacing it, and it can be used on any parameter binder (not just `self`):

- `fn set(self!)` desugars to `fn set[perm P](P self) where P is mut`.
- `fn f(x!: Vec[T])` desugars to `fn f[perm P, perm Q](P x: Q Vec[T]) where P is mut` (with a fresh perm var for `T` from the inline-`type T` rule, omitted here for clarity).

This is by the same "strictly more permissive at call sites" principle as the omitted-perm default: a body that needs mut access works equally well with any perm satisfying `is mut`, so we let callers pass any such perm rather than forcing a literal `Perm::Mt`.

Note that this is **different** from `!` on a *place expression* (e.g. `foo.bar!`), which is a concrete `mut[foo.bar]` / `.mut`. Binder `!` is attached to the parameter name, not to the type annotation. The `!` token is shared but the two contexts desugar differently:

| Context | Example | Desugars to |
|---|---|---|
| Place expression (value position) | `foo.bar!` | `foo.bar.mut` |
| Place expression (type position) | `foo.bar! String` | `mut[foo.bar] String` |
| Parameter binder | `self!` | fresh `P self` + `P is mut` predicate |

### `given` and `shared` on a parameter are concrete

Unlike `!`, the `given` and `shared` keywords on a parameter introduce **concrete** permissions (`Perm::Given`, `Perm::Shared`) and do **not** introduce a fresh perm variable. They are an exception to the implicit-perm rule.

```
fn f(value: given T)   # value: Perm::Given T — concrete
fn f(value: shared T)  # value: Perm::Shared T — concrete
fn f(value: T)         # value: P T for fresh P — implicit-perm rule
fn f(value!: T)        # value: P T where P is mut — implicit-perm rule + `!`
```

The asymmetry is deliberate: `given` and `shared` are the *named* concrete permissions in the language (they correspond to ownership transfer and refcounted sharing, respectively), and writing them explicitly on a parameter is a clear signal that the author wants exactly that permission, not "any perm that happens to be `is given`". `!` (and the implicit-perm default) are escape hatches *toward* polymorphism; `given`/`shared` are escape hatches *away* from it.

Examples:

```dada
class Vec[type T] {
    array: Array[T]; # class type parameters default to `given`
    len: u32;

    fn len(self) -> u32 {
        #  ^^^^ omitted perm => fresh unconstrained perm var
        #
        #  fn len[perm P](P self) -> u32
    }

    fn get(any self, index: u32) -> given[self] T {
        #  ^^^ `any` is equivalent to omitting; explicit-intent form
        #
        #  fn get[perm P, perm Q](P self, Q index: u32) -> given[self] T
    }

    fn contains(self, value: T) -> bool {
        #             ^^^^^^^^
        # Each omitted-perm parameter gets its *own* fresh perm var,
        # so `self` and `value` are unrelated permission-wise.
        #
        # fn contains[perm P, perm Q](P self, Q value) -> bool
    }

    fn set(self!, value: given T) {
        #      -         -----
        # `self!` adds an `is mut` predicate to the fresh perm var
        # for `self` (it composes with the implicit-perm rule
        # rather than replacing it). `given` and `shared` on a
        # parameter, by contrast, are *concrete* permissions — they
        # do not introduce a fresh perm var.
        #
        # fn set[perm P](P self, value: given T) where P is mut
    }

    fn pop(self!) -> Option[T] {
       #             ---------
       # Bare return types are preserved as written. In the current core
       # grammar, this plain form is already the owned return form.
    }
}
```

`ref` is also the default when accessing a place:

```dada
fn test(x: given String) {
    let y: ref[x] String = x;
}
```

### Sharing a permission across parameters

If you want two parameters to share a permission rather than each get their own fresh var, introduce a **named inline perm parameter** on first use and refer to it by name on subsequent uses:

```
fn f(x: perm P T, y: P T) { ... }
# fn f[perm P](P x: T, P y: T)
```

This mirrors how inline `type T` works (see below): the first occurrence introduces the binder, later occurrences are references. This is not expected to be a common pattern — most code wants the fully-independent default.

## in-line types and permissions

You can use in-line types and permissions in various places. They create a new parameter scoped to the innermost declaration:

```
fn foo(x: given Vec[type T]) {}
# fn foo[type T](x: given Vec[T]) {}
```

Inline declarations can carry where-clauses:

```
fn foo(x: given Vec[type T is copy]) {}
# fn foo[type T](x: given Vec[T]) where T is copy {}
```

And they can be anonymous:

```
fn foo(x: given Vec[type is copy]) {}
# fn foo[type T](x: given Vec[T]) where T is copy {}
```

The keyword `any` is short for an anonymous `perm` or `type` with no constraints, as needed:

```
fn foo(x: Iterator[any, any]) {}
# fn foo[type T, perm P](x: Iterator[T, P]) {}
```

### Where inline params are legal

Inline parameters are legal **only in function and method parameter types**, and they hoist to the enclosing fn/method binder. Everywhere else they are an error:

- ❌ **Return types** — `fn f(self) -> Vec[type T]` is an error.
- ❌ **Class field types** — `class C { xs: Vec[type T]; }` is an error, even though the class has a binder it could hoist to. Hiding a class's type parameters at a field-declaration site hurts readability; class parameters must be declared explicitly in the class header.
- ❌ **`let` bindings** — `let x: Vec[type T] = ...` is an error. There is no binder to hoist to.

Because `any` can stand for an anonymous inline `type` or `perm`, the same restriction applies to `any`: for example, `fn f() -> Vec[any]` is also an error.

### Scoping within a signature

Inline parameters are introduced in **source order**. Once an inline parameter has appeared, it is in scope for the rest of the signature: later parameter types, the return type, and the where-clause may all refer to it.

So this works:

```dada
fn foo(x: Vec[type T], y: T) -> T where T is copy
```

But this is an error:

```dada
fn foo(y: T, x: Vec[type T])
```

A named inline parameter may only be introduced once per declaration. Repeating the introduction is an error:

```dada
fn foo(x: Vec[type T], y: Option[type T]) # error: duplicate introduction of `T`
```

Anonymous inline parameters and `any` are always fresh; two occurrences introduce two distinct binders.

# Design

We introduce a set of **dada-surface** grammar terms that are wholly distinct from the underlying core grammar. The surface terms avoid formality's built-in binders and variables and instead use plain identifiers everywhere. The **elaborator** translates surface terms directly into core terms, constructing `Binder`s and `BoundVar`s as it goes. There is no print-and-reparse step.

## Surface is a strict superset of core

The surface grammar is designed so that **every existing core form is also a valid surface form with the same meaning**. The elaborator is the *identity* on core forms and only does work for the new sugars.

This is a load-bearing property: it means existing tests keep working unchanged, gives us free regression coverage on the elaborator's identity behavior, and lets us add features incrementally with no forced migration. See the FAQ entry "Why is the surface grammar a superset of core?" for the consequences this design unlocks.

This remains true even for the `given_from` → `given` transition, because the target core grammar also adopts `given[places]` and drops the old `given_from[...]` spelling.

## The elaborator is purely a frontend

Nothing downstream of `Program` knows that defaults or sugars exist. Specifically: the type checker, predicate solver, interpreter, and every judgment under `src/type_system/` and `src/interpreter/` operate on the core grammar exclusively and are unchanged by this work. The elaborator's contract is "surface `Program` in, core `Program` out"; once that boundary is crossed, the rest of the system is oblivious.

This is a deliberate, load-bearing architectural choice: it keeps the type system simple to reason about (only one grammar to teach, only one set of judgments to debug) and means the surface syntax can evolve without disturbing the formal model.

The codebase already has a placeholder for this boundary: the `ElaboratedProgram` newtype in `src/elaborator.rs`, currently produced by a no-op `elaborate` pass and consumed by `check_program`. As part of this work we will likely **revert** that newtype and replace it with a `SurfaceProgram` type that gets *converted* to a `Program` (rather than wrapped). The newtype was useful as a type-level reminder that elaboration must run, but once elaboration becomes a real translation between distinct types, the wrapper is redundant — the type signature `fn elaborate(SurfaceProgram) -> Program` says everything the newtype said, more directly.

## Why direct construction (and not string round-trip)

An earlier sketch proposed serializing the elaborated form to a string and reparsing it through the core parser, to avoid having to deal with formality's de Bruijn-indexed variables by hand. On closer inspection this is unnecessary: formality-core's binder API is high-level enough that direct construction is straightforward, and direct construction is strictly better on every other axis (source spans preserved, no printer/parser asymmetry, better diagnostics, less code in steady state).

## How binders are constructed

formality-core exposes `BoundVar::fresh(kind)` and `Binder::new(bound_vars, body)`. The de Bruijn indices are an implementation detail of `Binder`; callers never touch them. The existing codebase already uses this pattern — see `check_class_name` in `src/type_system/types.rs`:

```rust
let parameters: Vec<_> = (0..*n).map(|_| BoundVar::fresh(Kind::Ty)).collect();
Ok(Binder::new(parameters, vec![]))
```

The elaborator follows the same pattern: collect fresh `BoundVar`s for every implicit/inline parameter, build the body referring to them via `Perm::var(...)` / `Ty::var(...)`, then wrap everything in a `Binder::new`.

## Elaborating a method declaration (sketch)

For a surface declaration like `fn contains(self, value: T) -> bool`:

1. Walk the signature in **source order**, allocating fresh binders as each introducing occurrence is encountered:
   - implicit-perm parameters (`self`, `value`)
   - inline named type/perm params (`type T`, `perm P`)
   - anonymous inline params and `any` occurrences

   Record named ones in a `HashMap<Ident, BoundVar>` (the *name resolution map*) at the point they are introduced. Anonymous ones are not named and are referenced only at their introduction site.

2. Translate each later part of the signature using the names introduced so far. This enforces the scoping rule above: later parameter types, the return type, and the where-clause can refer to earlier inline parameters, but earlier parameter types cannot refer to names introduced later.

3. Wrap the resulting `MethodDeclBoundData` in `Binder::new(all_bound_vars, body)`.

Name resolution is needed regardless of which translation strategy we pick — even a string round-trip would need it for usable error messages — so this is not extra work.

## Surface AST shape

The surface terms use identifiers (not `BoundVar`/de Bruijn indices) and live in a parallel set of types under `src/surface/`. The elaborator lives in `src/elaborate/` and produces the core types in `src/grammar.rs` by walking the surface tree.

**Why duplication, not generics or sharing:** formality-core's `#[term]` macro does not accept generic type parameters, so we cannot define a single `Ty<V>` parameterized over surface vs core variable representation. Once any leaf type (here, `Ty` and `Perm`) needs to differ between surface and core, the difference propagates through every type that transitively contains it — which, in this codebase, is essentially the entire grammar. Rather than a fragile hybrid, we accept the duplication: the language is small enough that two copies of the grammar tree is manageable, and each grammar change has to be made in two places.

**Sharing rule:** types that are *trivially identical* between surface and core (no `Ty`/`Perm` reachability, no surface sugar) are reused directly from `src/grammar.rs`. Concretely:

- **Reused as-is:** `BinaryOp`, `Projection`, `Var`, `Place`, `FieldId`, `ValueId`, `TypeName`, `Kind`, `ParameterPredicate`, `VarianceKind`, `ClassPredicate`.
- **Duplicated under `src/surface/`:** `Program`, `ClassDecl`, `MethodDecl`, `FieldDecl`, `ParameterDecl`, `Predicate`, `Ty`, `Perm`, `Ascription`, `Block`, `Statement`, `Expr`, `PlaceExpr`, `Access` (the place-default-`.ref` rule means surface needs an extra "no access mode given" case), and the binder-wrapper structures.

**Binders:** where core uses formality's `Binder<T>`, surface uses its own representation: a `Vec<(Ident, Kind)>` of bound names alongside the body. The elaborator constructs the formality `Binder` via `BoundVar::fresh` + `Binder::new` after walking the body and resolving identifier references against the per-declaration name resolution map.

The elaborator is a single recursive walk over the surface tree. Each surface type has a `to_core(&self, names: &mut NameMap) -> Core` method (or equivalent free function); name resolution happens inline as identifier nodes are encountered. There is no separate "desugar then resolve" pass.

# Implementation plan

## Phase 1: `given_from` → `given` rename

This is the one non-additive change, and it applies to the language as a whole: the old `given_from[...]` spelling should be removed rather than preserved as a legacy alias.

**Step 0: spike.** Before doing the full sweep, prove out that the parser can actually distinguish `given` (concrete) from `given[places]` (place-based) in a small test case.

Then:

- Update the grammar so the language spells the place-based form as `given[places]`.
- Rename the corresponding core syntax to match.
- Rewrite every `given_from` occurrence under `src/**/tests/`, `book/`, and docs to `given`.
- Update any error messages mentioning the old keyword.
- Verify the full test suite is green before moving on.

This phase has no elaborator yet. It's pure renaming + parser tweak.

## Phase 2: elaborator skeleton

- Introduce `src/surface/` with the duplicated grammar types listed in the Design section ("Surface AST shape"). Reuse trivially-identical types from `src/grammar.rs`. Initially every surface form maps directly to its core counterpart — the elaborator is the identity (modulo the `Binder` construction step).
- Introduce `src/elaborate/` with the translator. Single recursive walk; threads a per-declaration name resolution map (`HashMap<Ident, BoundVar>`) used by every subsequent feature.
- Wire the pipeline: surface parse → elaborate → core `Program` → existing type checker (untouched). Likely revert the `ElaboratedProgram` newtype in favor of a `SurfaceProgram → Program` conversion (see Design).
- All existing tests must remain green: this phase is a no-op refactor of the parsing pipeline. `cargo test --all --workspace` passes with zero changes to any test file is the acceptance criterion.
- **Cost note:** this phase is the most boilerplate-heavy of the work. The duplication is mechanical, but it touches every grammar type that transitively contains `Ty`/`Perm`. Plan accordingly.

## Phase 3+: features, one per phase

Each of the following lands as its own phase. Each phase: extend the surface grammar with the new form, add the desugaring rule in the elaborator, write *new* tests in surface syntax exercising the form. Existing tests are not touched.

- `!` postfix sugar for `mut` (in permissions and in place expressions).
- Place expressions default to `.ref` when no access mode is given.
- `.share` on a place expands to `.give.share` (purely syntactic).
- Implicit/default permissions on function parameters (fresh unconstrained perm var per omitted-perm parameter).
- The `any` keyword as the explicit form of an omitted permission.
- Inline `type T` / `perm P` parameters in fn/method parameter types, with name resolution via the map from Phase 2.
- Anonymous inline params (`type`, `perm`) and `any` in type-argument positions.
- Bare return types are preserved as the existing plain core form; they are not elaborated to an explicit `given`.

Phases can be reordered if dependencies suggest a different sequence, but each one should remain individually reviewable.

# FAQ

## Why is the surface grammar a superset of core?

Designing the surface grammar as a strict superset of core (with the elaborator as the identity on core forms) has several consequences we like:

- **Zero forced migration.** Existing tests keep compiling unchanged. They serve as regression coverage for the elaborator's identity behavior on every core form in the corpus.
- **Incremental landing.** Each new feature is a small PR: extend the surface grammar, add one desugaring rule, write a few new tests. A bug in feature X cannot break tests that don't use feature X.
- **No escape hatch needed.** The core syntax *is* the escape hatch — it's always available, by construction, because it's a subset of surface. We don't need a `core!` macro or any other mechanism for tests that want to assert on post-elaboration form.
- **Cleaner correctness contract.** The elaborator's job can be stated as: "preserves the meaning of every core form; additionally, desugars these new forms to core." The identity-on-existing-tests property turns the entire existing test suite into a free regression suite for that contract.

The cost is that the surface grammar carries both old and new forms (e.g. both `mut[x]` and `x!`) indefinitely. We consider that an honest reflection of the migration story rather than a problem. Tests get rewritten to the new sugar opportunistically when someone touches them for unrelated reasons; there is no deadline.

## Why create implicit permission variables uniformly, even for types that look shared?

We briefly considered optimizing omitted parameter permissions away for obviously-shared-looking types, but the rule should stay uniform: an omitted parameter permission introduces a fresh perm variable.

The reason is that surface appearance is not enough. Even if a class is declared `shared class`, instantiations can still carry type arguments whose own permissions matter to later reasoning. For example, `Pair[String]` may look trivially shared, but treating omitted permissions specially for some apparent surface shapes quickly turns into a maze of ad hoc exceptions. The uniform rule is simpler for users, simpler for the elaborator, and leaves optimization to later phases if it ever proves worthwhile.

## What are things we still need to clarify?

A few design points are still open and should be settled before or during implementation:

- **Exact surface spelling for explicit permission arguments on non-`self` parameters.** The examples in this doc use forms like `x: given T` and `any self`, but we should state the full accepted surface grammar explicitly once the parser shape is nailed down.
- **Whether binder `!` can appear together with an explicit permission annotation.** The intent is clear when the permission is omitted (`x!: T`), but combinations like `x!: P T` have not been fully specified yet.
- **How diagnostics should present elaborated sugars.** In particular, `.share` desugars to `.give.share`; when the inserted `.give` is illegal, the user-facing error should talk about the original `.share`.
- **Parser strategy for `given` vs `given[...]`.** The design wants to remove `given_from` entirely, but we should confirm the best parser encoding before the implementation lands.
