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

Check `WIP.md` at the project root — it links the completed surface/core implementation
record (`md/wip/2026-10-surface-core.md`) and the ongoing soundness assessment
(`md/wip/2026-09-soundness-assessment.md`). The surface/core migration is complete;
`md/surface-syntax.md` describes the current syntax and explicit call arguments.

**When implementing a WIP plan, update the WIP doc as you go.** Mark items complete, add implementation notes, and record any deviations from the plan — all as part of the same commit that implements the change, not after the fact.

## Source Map

### `src/core/grammar.rs` + `src/core/grammar/`

Explicit core AST definitions using formality-core's `#[term]` macro. Concrete
permissions and identifier/binder infrastructure are shared with surface.
`grammar/source.rs` provides a structural source renderer (`source::program`),
with named binders and explicit parameter permissions for surface roundtrips.
Diagnostic `Debug` output is separate.

Key types: `Program`, `ClassDecl`, `MethodDecl`, `Ty`, `Perm`, `Expr`, `Statement`, `Place`, `Predicate`, `Access`.

**Permissions** (the `Perm` enum; independent `Shared` and nonempty `SharedFrom` share one syntax family):
- `given` or `given[]` — owned, unique
- `shared` or `shared[]` — owned, shared (refcounted)
- `shared[places]` — sharing from places
- `![places]` — borrowed mutable reference
- `given[places]` — moved permission (tracking source places)
- `or(P, Q, ...)` — one of several permissions in the same category

**Class predicates** (`ClassPredicate` enum, declared on classes):
- `class` — affine types (can have destructors)
- `struct` — mutable fields, can be shared; no nonempty destructor
- `shared struct` — value types, copyable when all generic arguments are shared; no nonempty destructor

**Access modes** (`Access` enum, used in place expressions like `x^`, `x.share`):
- `^` — give/move the value
- bare `place` or `place.share` — share from that place (`shared[place]`)
- `!` — mutable borrow

`drop place;` is a statement (`Statement::Drop`), not a value-producing access.
`Access::Drop` remains an internal checker access category.

Value sharing is a separate `Expr::ShareValue` operation: `place^.share` gives
the value, then shares it independently. `Access::SharePlace` shares a place.

**Parameter predicates** (`ParameterPredicate` enum): `shared`, `unique`, `owned`, `mut`, `struct`, `boxed`. Used in `where` clauses with syntax `Parameter is Predicate` (e.g., `P is shared`).

`shared` means shared, including shared place views; any shared permission can be duplicated. `struct` means shareable, and `owned` means fully owned. Require both `P is shared, P is owned` for fully owned shared values. The `shared` permission describes a shared value; `shared[d]` describes a shared value that references `d`.

**Variance predicates** (`VarianceKind` enum): `relative`, `atomic`. Also use `Parameter is Predicate` syntax (e.g., `T is relative`).

**Built-in expressions** (in `Expr` enum): `array_new`, `array_capacity`, `array_give`, `array_drop`, `array_write`, `size_of`.

### `src/surface/`

`grammar.rs` defines separate surface declaration, expression, and type ASTs.
`desugar.rs` contains structural `judgment_fn!` lowering into core. `parse_program`
is the common input path for the CLI and all program assertion helpers. Bare
outermost parameter types and `any T` generate fresh permission binders; `!T`
also requires `mut`. Receivers use the same defaults. Generated binders follow
explicit generics (receiver first, inputs left-to-right). Fields, returns, nested
types, and local annotations retain owned defaults. `[places] T` abbreviates
`shared[places] T` throughout surface types. Calls supply every generic argument;
there is no inference. See `src/core/grammar/method_diagnostics.rs` for resolved-call arity
and kind errors, including each slot's receiver/input association.

### `src/core/type_system.rs` + `src/core/type_system/`

Type checker entry point. `check_program()` is the top-level function.

Key modules:
- `env.rs` — `Env` struct: typing context with variable bindings, predicate assumptions, scope management
- `subtypes.rs` — subtyping rules
- `predicates.rs` — predicate proving (shared, unique, owned, mut, etc.)
- `redperms.rs` + `redperms/` — reduced permissions (permission normalization)
- `pop_normalize.rs` — resolves return permissions before call temporaries leave scope
- `call_origins.rs` — protects caller origins from callee-name capture during generic instantiation
- `liveness.rs` — liveness analysis
- `accesses.rs` — access mode checking
- `places.rs` — place type computation
- `expressions.rs`, `statements.rs`, `blocks.rs` — expression/statement type checking
- `methods.rs`, `classes.rs` — declaration checking

Uses formality-core's `judgment_fn!` macro for inference rules throughout.

### `src/core/interpreter/mod.rs` + `src/core/interpreter/`

Interpreter that evaluates Dada programs. Operates on a flat word-based memory model.

Key concepts:
- `Alloc` — flat array of `Word` values (the heap representation)
- `Word` — `Flags(Flags)`, `Pointer(Pointer)`, `Int(usize)`, `Lease(Pointer)`, `Uninitialized`
- `Flags` — `Given`, `SharedOwned`, `SharedPlace`
- `Outcome` — `Value(ObjectValue)`, `Break`, `Return(ObjectValue)` (control flow)
- Boxed types (including `Array[T]`) use a `[Flags, Pointer]` wrapper layout; the pointer references a heap allocation
- Array layout: `[refcount, capacity, elements...]`
- Types flow through evaluation as `ObjectValue { pointer, ty }` — allocations carry no type information

### `src/test_util.rs`

Test macros and helpers all parse surface and lower to core first:
- `assert_desugars!({ surface } => { core })` — compare the lowered AST with an
  independently parsed core expectation, modulo bound-variable names; also accepts
  two string expressions. Checks desugaring only, without checking or interpreting.
- `assert_ok!` — type-check succeeds
- `assert_err!` — type-check fails with expected error
- `assert_interpret!` — type-check + interpret succeeds, compare snapshot (output lines + result + heap)
- `assert_interpret_only!` — lower and interpret without type-checking (for testing programs the type checker rejects)
- `assert_interpret_fault!` — lower and interpret without type-checking, expect a fault

### `src/lib.rs`

Language declaration (`declare_language!`) including the KEYWORDS list. Words in KEYWORDS are reserved and cannot be used as identifiers.

## Test Organization

- **Property tests**: `src/properties/` — test-only modules named for the property
  they exercise. The leading `//!` Markdown header is the authoritative property
  statement, including scope, evidence, and any candidate lemma (not a proved theorem).
  `receiver_permissions_have_valid_origins` checks signature origins and rejects
  malformed programmatic receiver permissions after surface lowering.
  `call_generic_origins_are_hygienic` checks that caller places in generic
  arguments survive callee renaming and retain returned-value dependencies.
  `explicit_ownership_preserves_generic_types` checks that the identity `given`
  permission requires no relative bound, while nonidentity permissions still do.
  `parameter_permissions_are_explicit_at_calls` checks generated permissions,
  explicit call arguments, diagnostics, and mutable capability requirements.
  `unique_ownership_requires_unique_and_owned` checks the conjunction of those
  predicates, including generic forwarding and rejection controls.
  `only_classes_have_destructors` checks class/struct destructor restrictions.
  `drops_respect_live_dependencies` checks explicit drops before/after the last
  use of a shared view and destructor execution.
  `independent_sharing_is_owned_and_duplicable` checks empty-origin sharing and
  its owned/shared predicates, and rejects exclusivity.
  `moves_preserve_dependencies` contains the former `move_tracking` tests.
  `given_from_duplication_requires_shared_origins` contains the duplication cases
  extracted from `predicate_quantifiers`, plus the both-unique rejection case;
  mutation and vocabulary tests remain in `predicate_quantifiers`. The property
  also covers projected origins and shared place origins. Dependency preservation
  after duplication now belongs to `given_from_preserves_origin_dependencies`.
  `given_from_mut_requires_mut_origins` checks the distinct `mut` predicate using
  complete Dada programs with calls requiring `P is mut`. Its `mod.rs` header
  defines the property; `direct`, `fields`, `nested_fields`, and `stored_fields`
  submodules contain explicit positive/negative cases. Unique ownership permits
  field assignment but does not itself satisfy `mut`; assignment tests are separate.
  `given_from_owned_requires_owned_origins` and
  `given_from_unique_requires_unique_origins` follow the same module layout, with full
  direct-origin pairs and selected projected/stored-field cases. `owned` includes
  unique and shared ownership; `unique` includes unique owners and mutable leases.
  `sharing_does_not_grant_mut` covers shared views of owners and leases, including
  cancellation of a dead intermediate lease. `given_from_preserves_origin_dependencies`
  covers restrictions inherited from origin types, surviving duplicates/transfers,
  projected origins, last-use release, and static referent relocation.
  `call_returns` groups four independently documented properties:
  `ownership_can_escape`, `borrows_of_consumed_arguments_cannot_escape`,
  `forwarded_borrows_keep_referents_borrowed`, and
  `all_possible_return_referents_remain_borrowed`. These contain the former
  checker `normalization` tests plus cases of access through surviving return
  dependencies. The parent is an organizational module, not a broader property.
  Ownership-return examples cover explicit `given` results as well as
  permissions resolved through `given[places]`.
  All accepted `call_returns` programs also execute with `assert_interpret!`;
  rejected programs retain checker-error snapshots.
  Runtime normalization tests and local `pop_normalize` tests remain separate;
  direct runtime frame tests inspect result types and caller bindings without
  checking the individual call expressions, alongside two end-to-end examples.
- Prefer end-to-end semantic tests: a readable Dada program that should or should
  not type-check. For valid programs, default to `assert_interpret!` so they are
  also executed and their output/result/heap checked. Use `assert_ok!` when a case
  intentionally tests only static behavior or cannot meaningfully execute, and
  explain that limitation. Use `assert_err!` for checker rejection. Avoid direct
  predicate calls or generated-program helpers that obscure what a test checks.
  When useful, pair a rejecting program with a control removing only the relevant
  requirement.
  When testing returned values, use the result after binding it (for example,
  read a field or pass it to a consumer), rather than checking only that the call
  can initialize a local.
- New semantic tests should have a primary property home. Existing feature-based
  tests are migrated incrementally; parser/tooling tests can retain their own homes.
  Property changes update the module prose alongside the tests. Known violations
  should link a tracking GitHub issue and be distinguished from supporting evidence.
  Explanatory examples can belong to a property and retain their snippet anchors.

- **Type system tests**: `src/core/type_system/tests/` — test files organized by feature (e.g., `cancellation.rs`, `given_classes.rs`, `subtyping/`)
- **Interpreter tests**: `src/core/interpreter/tests/` — test files organized by feature (e.g., `array.rs`, `place_ops.rs`, `share.rs`)

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
- **Prefix ambiguity**: If one variant's keyword is a prefix of another's in the same enum (e.g., `given` vs `given[x]`), the parser silently matches the shorter one. Use a single custom parse branch with optional origins, as the `given` permission parser does.
- **Arc clone in judgment_fn**: Fields declared as `Arc<T>` become `&Arc<T>` in judgment rules. `.clone()` gives `Arc<T>`, not `T`. Use `T::clone(x)` for deref coercion to get `T`.
- **`for_all` vs `in`**: `(x in collection)` is existential (there exists). `for_all(x in coll) with(acc)` is universal (for all).
