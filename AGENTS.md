# dada-model

Formal model for the Dada programming language, built on [formality-core](https://rust-lang.github.io/a-mir-formality/formality_core.html). Implements a type system and interpreter for Dada's permission-based ownership model.

**Keep this file up to date.** If you rename syntax, add modules, change test macros, or otherwise invalidate something described here, update this file as part of the same change.

## Build and Test

```bash
cargo test --all --workspace
```

Snapshot tests use `expect_test`. To auto-update snapshots after intentional changes:

```bash
UPDATE_EXPECT=1 cargo test --all --all-targets
```

## Work In Progress

Check `WIP.md` at the project root — it points to the current assessment or implementation plan (currently `md/wip/2026-09-soundness-assessment.md`).

**When implementing a WIP plan, update the WIP doc as you go.** Mark items complete, add implementation notes, and record any deviations from the plan — all as part of the same commit that implements the change, not after the fact.

## Source Map

### `src/grammar.rs` + `src/grammar/`

AST definitions using formality-core's `#[term]` macro. All Dada syntax lives here.

Key types: `Program`, `ClassDecl`, `MethodDecl`, `Ty`, `Perm`, `Expr`, `Statement`, `Place`, `Predicate`, `Access`.

**Permissions** (the `Perm` enum):
- `given` — owned, unique
- `shared` — owned, shared (refcounted)
- `ref[places]` — borrowed reference
- `mut[places]` — borrowed mutable reference
- `given_from[places]` — moved permission (tracking source places)
- `or(P, Q, ...)` — one of several permissions in the same category

**Class predicates** (`ClassPredicate` enum, declared on classes):
- `given class` — affine types (can have destructors)
- `class` (default) — mutable fields, can be shared
- `shared class` — value types, always copyable

**Access modes** (`Access` enum, used in place expressions like `x.give`, `x.ref`):
- `.give` — give/move the value
- `.ref` — borrow
- `.mut` — mutable borrow
- `.drop` — drop the value

**Parameter predicates** (`ParameterPredicate` enum): `shared`, `move`, `owned`, `mut`, `given`, `share`, `boxed`. Used in `where` clauses with syntax `Parameter is Predicate` (e.g., `P is shared`).

`shared` means shared, including borrowed references; any shared permission can be duplicated. `share` means shareable, and `owned` means fully owned. Require both `P is shared, P is owned` for fully owned shared values. The `shared` permission describes a shared value; `ref[d]` describes a shared value that references `d`.

**Variance predicates** (`VarianceKind` enum): `relative`, `atomic`. Also use `Parameter is Predicate` syntax (e.g., `T is relative`).

**Built-in expressions** (in `Expr` enum): `array_new`, `array_capacity`, `array_give`, `array_drop`, `array_write`, `size_of`.

### `src/type_system.rs` + `src/type_system/`

Type checker entry point. `check_program()` is the top-level function.

Key modules:
- `env.rs` — `Env` struct: typing context with variable bindings, predicate assumptions, scope management
- `subtypes.rs` — subtyping rules
- `predicates.rs` — predicate proving (shared, move, owned, mut, etc.)
- `redperms.rs` + `redperms/` — reduced permissions (permission normalization)
- `pop_normalize.rs` — resolves return permissions before call temporaries leave scope
- `liveness.rs` — liveness analysis
- `accesses.rs` — access mode checking
- `places.rs` — place type computation
- `expressions.rs`, `statements.rs`, `blocks.rs` — expression/statement type checking
- `methods.rs`, `classes.rs` — declaration checking

Uses formality-core's `judgment_fn!` macro for inference rules throughout.

### `src/interpreter/mod.rs` + `src/interpreter/`

Interpreter that evaluates Dada programs. Operates on a flat word-based memory model.

Key concepts:
- `Alloc` — flat array of `Word` values (the heap representation)
- `Word` — `Flags(Flags)`, `Pointer(Pointer)`, `Int(usize)`, `MutRef(Pointer)`, `Uninitialized`
- `Flags` — `Given`, `Shared`, `Ref`, `Dropped`
- `Outcome` — `Value(ObjectValue)`, `Break`, `Return(ObjectValue)` (control flow)
- Boxed types (including `Array[T]`) use a `[Flags, Pointer]` wrapper layout; the pointer references a heap allocation
- Array layout: `[refcount, capacity, elements...]`
- Types flow through evaluation as `ObjectValue { pointer, ty }` — allocations carry no type information

### `src/test_util.rs`

Test macros and helpers:
- `assert_ok!` — type-check succeeds
- `assert_err!` — type-check fails with expected error
- `assert_interpret!` — type-check + interpret succeeds, compare snapshot (output lines + result + heap)
- `assert_interpret_only!` — interpret without type-checking (for testing programs the type checker rejects)
- `assert_interpret_fault!` — interpret without type-checking, expect a fault

### `src/lib.rs`

Language declaration (`declare_language!`) including the KEYWORDS list. Words in KEYWORDS are reserved and cannot be used as identifiers.

## Test Organization

- **Property tests**: `src/properties/` — test-only modules named for the property
  they exercise. The leading `//!` Markdown header is the authoritative property
  statement, including scope, evidence, and any candidate lemma (not a proved theorem).
  `moves_preserve_dependencies` contains the former `move_tracking` tests.
  `given_from_duplication_requires_shared_origins` contains the duplication cases
  extracted from `predicate_quantifiers`, plus the both-unique rejection case;
  mutation and vocabulary tests remain in `predicate_quantifiers`. The property
  also covers projected origins, borrowed `ref` origins, and the preservation of
  referent restrictions after duplication.
- New semantic tests should have a primary property home. Existing feature-based
  tests are migrated incrementally; parser/tooling tests can retain their own homes.
  Property changes update the module prose alongside the tests. Known violations
  should link a tracking GitHub issue and be distinguished from supporting evidence.
  Explanatory examples can belong to a property and retain their snippet anchors.

- **Type system tests**: `src/type_system/tests/` — test files organized by feature (e.g., `cancellation.rs`, `given_classes.rs`, `subtyping/`)
- **Interpreter tests**: `src/interpreter/tests/` — test files organized by feature (e.g., `array.rs`, `place_ops.rs`, `share.rs`)

Both use `expect_test` for snapshot testing. Type system tests use `assert_ok!`/`assert_err!`. Interpreter tests use `assert_interpret!`/`assert_interpret_only!`/`assert_interpret_fault!`.

## Documentation

- `md/` — mdBook documentation on the type system. Build with `mdbook build`.
- `md/wip/` — working design documents for in-progress features; the property
  extraction status is in `md/wip/test-anchors.md`.
- `mdbook-judgment/` — workspace package extracting rules, snippets, and property
  documentation. A standalone, unindented `{{property moves_preserve_dependencies}}`
  inserts the module's leading `//!` header as Markdown with a source link.
  IDs are paths relative to `src/properties`, separated by `::`; both `foo.rs`
  and `foo/mod.rs` are supported. Supporting test submodules need not be properties.
  Start the file with its header (leading blank lines are allowed); prefix blank
  documentation lines with `//!` too. Property references inside fenced or indented
  code stay literal. Missing/ambiguous modules and missing headers fail the build.
- Use **property** for a semantic claim and **anchor** for an existing source-snippet
  marker. Define a property once in its test module and include it in the book.
  The book describes the committed model, including clearly identified limitations;
  proposed changes and improvement plans belong in GitHub issues. Existing WIP
  chapters are legacy content awaiting a separate migration.

## formality-core Gotchas

Things that cause confusing errors if you don't know about them:

- **KEYWORDS reservation**: Adding a word to the KEYWORDS list in `declare_language!` (in `src/lib.rs`) prevents it from being used as an identifier anywhere. Grammar keywords (`#[grammar(x)]` on enum variants) work without being in KEYWORDS. Only add to KEYWORDS when you want to block identifier use.
- **Parser ambiguity**: Two `#[term]` enums with variants resolving to the same keyword in the same parsing context cause a runtime panic ("ambiguous parse"). Fix with `#[grammar(distinct_keyword)]`.
- **Prefix ambiguity**: If one variant's keyword is a prefix of another's in the same enum (e.g., `given` vs `given[x]`), the parser silently matches the shorter one. Use a distinct keyword (e.g., `given_from`).
- **Arc clone in judgment_fn**: Fields declared as `Arc<T>` become `&Arc<T>` in judgment rules. `.clone()` gives `Arc<T>`, not `T`. Use `T::clone(x)` for deref coercion to get `T`.
- **`for_all` vs `in`**: `(x in collection)` is existential (there exists). `for_all(x in coll) with(acc)` is universal (for all).
