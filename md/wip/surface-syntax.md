# Status note

This document describes the **target state** for Dada's surface syntax and elaboration model.

The **current state** is narrower:

- the accepted grammar is still essentially the existing core syntax
- the final "types checked" phase exists today
- the earlier elaboration phases described below are design targets, not fully-implemented passes

The "Commit N" section later in this document is the incremental rollout plan from the current implementation to that target design.

This effort is mildly blocked on a related surface-syntax question: we also need to decide how permission and other parameters are written and resolved at **method call sites**, not just in declarations. That turns out to be a non-trivial part of the design/elaboration story, so the overall project is somewhat larger in scope than this doc originally assumed. It is not fully blocked, but it is not quite as self-contained as it first appeared.

# Features in scope

- `!` as postfix sugar for `mut` (in permissions and place expressions)
- Place expressions default to `.ref` when no access mode is given
- `.share` applied to a place expands to `.give.share`
- Implicit/default permissions on function parameters, while preserving bare field/return types
- Inline type and permission parameters, named or anonymous
- `exists[...] { ... }` blocks for explicit elaboration variables

# Goal

Match Dada's planned surface syntax, taking advantage of the new elaborator and improvements in formality's parsing capabilities.

# Elaboration terminology and scope

This document is about **elaboration**, not about extending the core type checker with inference rules.

Elaboration serves two roles:

1. Add in missing information that the surface language permits the user to omit.
2. Rewrite surface conveniences into explicit core forms.

These phases are deterministic and meaningful: they make commitments that were not written explicitly by the user. They are therefore not merely "desugaring", even though some phases do perform ordinary sugar expansion.

The key architectural point is that elaboration is allowed to produce a candidate explicit core program that is **not yet known to be sound**. Soundness remains the responsibility of the existing type checker, which runs only after elaboration is complete. In other words:

- elaboration reconstructs a fully explicit program
- type checking validates that reconstructed program

This is intentionally different from baking full inference directly into the core typing judgments.

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

## implicit permissions on function parameters

Every function parameter with no explicit permission gets a **fresh, unconstrained permission variable**, hoisted to the enclosing fn/method binder. `self` is not special — the same rule applies to every parameter. Each omitted-perm parameter gets its *own* fresh variable, so they are independent.

Bare field types and bare return types are preserved exactly as written. In today's core language those plain forms are the existing owned form (for example `-> String` remains `-> String`, rather than being elaborated to an explicit `given String`). Parameters are different: an omitted permission on a parameter introduces a fresh perm variable.

Why fully-unconstrained rather than e.g. defaulting to `is ref`? `perm P` and `perm P where P is ref` admit exactly the same operations on the parameter (in both cases the body must assume the value might be a reference), but the unconstrained form lets *callers* pass anything — owned, shared, mut, ref. Defaulting to fully unconstrained is therefore strictly more ergonomic at call sites with no cost in the body.

### `!` on a parameter binder

Postfix `!` on a parameter binder is sugar for prepending an anonymous `(perm is mut)` binder to that parameter's type. It **composes** with the implicit-perm rule rather than replacing it, and it can be used on any parameter binder (not just `self`):

- `fn f(x!: Vec[T])` desugars to `fn f(x: (perm is mut) Vec[T])`.
- `fn set(self!)` is the same rule, but `self` is written in the receiver position rather than as an ordinary `name: Type` parameter.

This is by the same "strictly more permissive at call sites" principle as the omitted-perm default: a body that needs mut access works equally well with any perm satisfying `is mut`, so we let callers pass any such perm rather than forcing a literal `Perm::Mt`.

Note that this is **different** from `!` on a *place expression* (e.g. `foo.bar!`), which is a concrete `mut[foo.bar]` / `.mut`. Binder `!` is attached to the parameter name, not to the type annotation. The `!` token is shared but the two contexts desugar differently:

| Context | Example | Desugars to |
|---|---|---|
| Place expression (value position) | `foo.bar!` | `foo.bar.mut` |
| Place expression (type position) | `foo.bar! String` | `mut[foo.bar] String` |
| Parameter binder | `x!: T` | `x: (perm is mut) T` |

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

    fn get(self, index: u32) -> given[self] T {
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

## `exists[...] { ... }` blocks

The surface language also admits explicit block-scoped elaboration variables:

```dada
exists[type T] {
    let x: (T, T) = (foo, bar)
}
```

This is a real surface-language construct, not just compiler-internal notation. It lets users state that there exists a choice of type and/or permission arguments under which the block elaborates.

The binder accepts any mix of type and permission variables:

```dada
exists[type T, perm P] {
    ...
}
```

These variables are scoped over the block body. They are intended for expression/block-level elaboration only. Signature-level omission and inline signature binders still follow the rules described below and are elaborated separately.

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

Permissions work the same way:

```
fn foo(x: Iterator[type, perm is shared]) {}
# fn foo[type T, perm P](x: Iterator[T, P]) where P is shared {}
```

### Where inline params are legal

Within signatures, inline parameters are legal **only in function and method parameter types**, and they hoist to the enclosing fn/method binder. They are not legal in other signature positions:

- ❌ **Return types** — `fn f(self) -> Vec[type T]` is an error.
- ❌ **Class field types** — `class C { xs: Vec[type T]; }` is an error, even though the class has a binder it could hoist to. Hiding a class's type parameters at a field-declaration site hurts readability; class parameters must be declared explicitly in the class header.
- ❌ **`let` type ascriptions** — `let x: Vec[type T] = ...` is an error as written. Inside function bodies, block-scoped elaboration variables must be introduced explicitly via `type` / `perm` statements or `exists[...] { ... }`, rather than implicitly from inside a `let` type.

### Scoping within a signature

Inline parameters are introduced in **source order**. Once an inline parameter has appeared, it is in scope for the rest of the signature: later parameter types, the return type, and the where-clause may all refer to it.

So this works:

```dada
fn foo(x: Vec[type T], y: T) -> T where T is copy
```

The same declaration-level binder may not introduce the same name twice. This is an error, just as it would be in an explicit binder list:

```dada
fn foo(x: Vec[type T], y: Option[type T]) # error: duplicate introduction of `T`
```

An inline binder only puts the name in scope from that point onward, so this is also an error:

```dada
fn foo(t: T, vec: Vec[type T]) # error: first `T` is not in scope
```

If an outer `T` is already in scope, later introduction of an inline `T` is allowed but confusing:

```dada
class T
fn foo(t: T, vec: Vec[type T]) # OK, but should lint
```

In that example, the type of `t` is the outer `T`, while the element type of `vec` is the later inline `T`. Those are distinct types despite sharing a name.

Anonymous inline parameters are always fresh; two occurrences introduce two distinct binders.

### Inline predicates

Both named and anonymous inline binders may carry `is` predicates:

```dada
fn foo(x: Vec[type T is shared]) {}
fn foo(x: Vec[type is copy]) {}
fn foo(x: (perm P is mut) String) {}
fn foo(x: (perm is mut) String) {}
```

When an anonymous inline binder appears in a syntactically ambiguous prefix position, parentheses may be required:

```dada
fn foo(x: perm Foo) {}
# parsed as `x: (perm Foo)` and therefore rejected: a type is expected

fn foo(x: (perm) Foo) {}
# anonymous inline permission binder
```

In bracketed type-argument positions no extra parentheses are needed:

```dada
fn foo(x: Vec[type is copy]) {}
```

This is a place where formality-core's reject mechanism may be useful to keep the grammar simple while rejecting the ambiguous parse cleanly.

## `type` and `perm` in function bodies

Inside a function body, `type` and `perm` introductions are also legal. In that context they do **not** hoist to the enclosing declaration binder; instead, they elaborate to a block-scoped existential.

Examples:

```dada
type T;
perm P;
```

These are surface shorthands for introducing fresh block-scoped elaboration variables, equivalent in spirit to wrapping the surrounding region in `exists[...]`.

# Design

We use a **single union grammar**. The accepted input language is a strict superset of core: every core program is also a valid surface program, but the surface language additionally permits omitted information, explicit `exists[...] { ... }` blocks, and various sugars.

Elaboration proceeds in phases that progressively eliminate these surface-only forms until the program is in the existing core fragment. Later phases assume earlier ones have already run.

The current phase split is:

1. **Surface**
2. **Signature elaborated**
3. **Types elaborated**
4. **Permissions elaborated**
5. **Types checked**

The last phase is the type checker we already have today. The earlier phases are frontend elaboration.

The union grammar is only the parser-level story. Each phase also has a corresponding **wellformedness judgment** describing exactly which forms are permitted at that stage. The intended shape is:

- a broad parsed grammar that can represent every phase
- a judgment per phase characterizing the fragment admitted there
- an elaboration judgment from one phase to the next

So, for example, we expect judgments along the lines of `wf_surface`, `wf_signature_elaborated`, `wf_types_elaborated`, and `wf_permissions_elaborated`. The elaboration pipeline should establish these judgments at each boundary: if phase 1 produces a "signature elaborated" program, that output should satisfy `wf_signature_elaborated`, and so on.

These judgments are not just specification machinery. They should also be used as implementation-time sanity checks at phase boundaries, e.g. assertions in the style of `assert!(wf_signature_elaborated(...).is_proven())`, so that leaked earlier-phase forms fail immediately instead of surfacing later as confusing bugs.

## Surface is a strict superset of core

The accepted input grammar is designed so that **every existing core form is also a valid surface form with the same meaning**.

This is a load-bearing property: it means existing tests keep working unchanged, gives us free regression coverage on the elaboration pipeline's fixed-point behavior on core programs, and lets us add features incrementally with no forced migration. See the FAQ entry "Why is the surface grammar a superset of core?" for the consequences this design unlocks.

## The elaborator is purely a frontend

Nothing downstream of the final elaborated `Program` knows that defaults, `exists` binders, or sugars exist. Specifically: the type checker, predicate solver, interpreter, and every judgment under `src/type_system/` and `src/interpreter/` operate on the core grammar exclusively and are unchanged by this work. The elaborator's contract is still "surface `Program` in, core `Program` out"; once that boundary is crossed, the rest of the system is oblivious.

This is a deliberate, load-bearing architectural choice: it keeps the type system simple to reason about (only one grammar to teach, only one set of judgments to debug) and means the surface syntax can evolve without disturbing the formal model.

The codebase already has a placeholder for this boundary: the `ElaboratedProgram` newtype in `src/elaborator.rs`, currently produced by a no-op `elaborate` pass and consumed by `check_program`. The final shape may keep or replace that wrapper, but the architectural boundary remains the same: elaboration finishes before type checking begins.

## Phase boundaries

The phases are distinguished by which surface-only forms are still permitted. In the intended formalization, each bullet below corresponds to a wellformedness judgment for that phase.

### 1. Surface

This is the broadest accepted grammar. It includes:

- all current core forms
- surface sugars like postfix `!` and implicit `.ref`
- omitted signature information governed by the rules above
- explicit block-scoped `exists[...] { ... }` binders

### 2. Signature elaborated

This phase resolves signature-level omission and inline signature sugar. In particular:

- omitted parameter permissions are made explicit
- inline `type` / `perm` parameters are hoisted to the enclosing declaration binder
- anonymous inline parameters in signature positions are replaced by fresh explicit binders

This phase is still frontend elaboration, not type checking. It may introduce explicit binders and internal elaboration variables, but it does not yet need to justify them semantically.

### 3. Types elaborated

This phase commits to type structure. Intuitively, it chooses the type "spine" while still allowing permissions to remain unresolved.

Block-scoped `exists[type ...]` binders may be discharged here. The output of this phase should have fully explicit type structure, though permission unknowns may still appear inside that structure.

### 4. Permissions elaborated

This phase resolves the remaining permission unknowns and discharges `exists[perm ...]` binders.

Its output is a fully explicit core program with no surface-only omission or existential forms remaining.

### 5. Types checked

This is the existing type checker. It validates the fully elaborated core program. Any soundness failures are reported here, not during the earlier elaboration phases.

## Binders and internal representations

The elaboration phases will still need to construct formality-core `Binder`s and `BoundVar`s when they produce fully explicit core declarations. formality-core exposes `BoundVar::fresh(kind)` and `Binder::new(bound_vars, body)`, and the existing codebase already uses this style.

At the same time, not every intermediate phase has to be represented as a separate AST family. The current direction is to keep a single broad grammar and define each phase by which forms remain admissible, rather than by maintaining a completely separate `src/surface/` tree.

Some phases may still find it convenient to use internal helper forms or judgments to represent partially elaborated programs. The load-bearing point is the phase boundary, not whether each phase gets its own Rust enum tree.

# Implementation plan

This section is an implementation rollout plan from the current codebase to the target-state design described above. These are **commits**, not the architectural elaboration phases.

## Commit 1: elaboration skeleton

- Introduce the multi-phase elaboration pipeline:
  - surface
  - signature elaborated
  - types elaborated
  - permissions elaborated
  - types checked
- Wire the parser/elaborator/type-checker pipeline so that elaboration runs before `check_program`.
- Keep core programs as fixed points of the early phases.
- Acceptance criterion: existing tests keep passing unchanged.

## Commit 2: signature elaboration

- Implement declaration-signature elaboration for:
  - omitted parameter permissions
  - parameter-binder `!`
  - inline `type` / `perm`
  - anonymous inline params
  - inline `is` predicates on named and anonymous binders
- Preserve the existing rule that bare field and return types remain as written.
- Add tests showing that signature omission becomes explicit before later elaboration phases.

## Commit 3: type elaboration

- Add the expression/block-level `exists[...] { ... }` form to the implementation.
- Add body-level `type` / `perm` introductions as sugar for block-scoped existentials.
- Elaborate type structure, discharging type existentials and choosing explicit type spines.
- Permit permission unknowns to remain after this phase.
- Add tests covering block-scoped `exists[type ...]`.

## Commit 4: permission elaboration

- Elaborate remaining permission unknowns into explicit permissions.
- Discharge `exists[perm ...]`.
- Keep the solver deterministic and scoped by the variables available at each use site.
- Add tests covering both explicit `exists[perm ...]` blocks and permissions introduced implicitly by earlier phases.

## Commit 5+: remaining sugars and diagnostics

These surface forms still need to be implemented as part of the overall effort:

- `!` postfix sugar for `mut` in place expressions and permission positions
- place expressions defaulting to `.ref`
- `.share` on a place expanding to `.give.share`
- diagnostic provenance for user-written surface forms that elaborate into inserted core operations

Commits can be reordered or split further if dependencies suggest a different sequence, but the 5-stage architecture above is the intended model.

# FAQ

## Why is the surface grammar a superset of core?

Designing the accepted input grammar as a strict superset of core has several consequences we like:

- **Zero forced migration.** Existing tests keep compiling unchanged. They serve as regression coverage for the fact that core programs are fixed points of the elaboration pipeline.
- **Incremental landing.** Each new feature is a small PR: accept a new surface form, elaborate it away in the appropriate phase, and add a few new tests. A bug in feature X cannot break tests that don't use feature X.
- **No escape hatch needed.** The core syntax *is* the escape hatch — it's always available, by construction, because it's a subset of surface. We don't need a `core!` macro or any other mechanism for tests that want to assert on post-elaboration form.
- **Cleaner correctness contract.** The elaborator's job can be stated as: "turn any accepted surface program into an explicit core program; leave already-core programs unchanged." The identity-on-existing-tests property turns the entire existing test suite into a free regression suite for that contract.

The cost is that the surface grammar carries both old and new forms (e.g. both `mut[x]` and `x!`) indefinitely. We consider that an honest reflection of the migration story rather than a problem. Tests get rewritten to the new sugar opportunistically when someone touches them for unrelated reasons; there is no deadline.

## Why create implicit permission variables uniformly, even for types that look shared?

We briefly considered optimizing omitted parameter permissions away for obviously-shared-looking types, but the rule should stay uniform: an omitted parameter permission introduces a fresh perm variable.

The reason is that surface appearance is not enough. Even if a class is declared `shared class`, instantiations can still carry type arguments whose own permissions matter to later reasoning. For example, `Pair[String]` may look trivially shared, but treating omitted permissions specially for some apparent surface shapes quickly turns into a maze of ad hoc exceptions. The uniform rule is simpler for users, simpler for the elaborator, and leaves optimization to later phases if it ever proves worthwhile.

## What are things we still need to clarify?

A few design points are still open and should be settled before or during implementation:

- **Exact surface spelling for explicit permission arguments on non-`self` parameters.** The examples in this doc use forms like `x: given T`, `x: perm P T`, and `x: (perm) T`, but we should state the full accepted surface grammar explicitly once the parser shape is nailed down.
- **Whether binder `!` can appear together with an explicit permission annotation.** The intent is clear when the permission is omitted (`x!: T`), but combinations like `x!: P T` have not been fully specified yet.
- **Precise phase interfaces.** We now have the five high-level stages, but each one still needs a sharper contract stating exactly which forms are admitted in its input and guaranteed absent in its output.
- **Algorithm details for type elaboration.** The current plan is "infer the type spine first, leaving permission variables in place", but the exact local-vs-global strategy still needs to be written down.
- **Algorithm details for permission elaboration.** The current plan is bound propagation over scoped permission variables with deterministic choice, but the concrete solving strategy still needs to be specified.
- **How diagnostics should present elaborated sugars.** In particular, `.share` desugars to `.give.share`; when the inserted `.give` is illegal, the user-facing error should talk about the original `.share`.
