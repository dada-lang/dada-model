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

Check `WIP.md` at the project root — it points to the active implementation plan (currently `md/wip/vec.md`).

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

**Class predicates** (`ClassPredicate` enum, declared on classes):
- `given class` — affine types (can have destructors)
- `class` (default) — mutable fields, can be shared
- `shared class` — value types, always copyable

**Access modes** (`Access` enum, used in place expressions like `x.give`, `x.ref`):
- `.give` — give/move the value
- `.ref` — borrow
- `.mut` — mutable borrow
- `.drop` — drop the value

**Parameter predicates** (`ParameterPredicate` enum): `copy`, `move`, `owned`, `mut`, `given`, `shared`, `share`, `boxed`. Used in `where` clauses with syntax `Parameter is Predicate` (e.g., `P is copy`).

**Variance predicates** (`VarianceKind` enum): `relative`, `atomic`. Also use `Parameter is Predicate` syntax (e.g., `T is relative`).

**Built-in expressions** (in `Expr` enum): `array_new`, `array_capacity`, `array_give`, `array_drop`, `array_write`, `size_of`.

### `src/type_system.rs` + `src/type_system/`

Type checker entry point. `check_program()` is the top-level function.

Key modules:
- `env.rs` — `Env` struct: typing context with variable bindings, predicate assumptions, scope management
- `subtypes.rs` — subtyping rules
- `predicates.rs` — predicate proving (copy, move, owned, mut, etc.)
- `redperms.rs` + `redperms/` — reduced permissions (permission normalization)
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

- **Type system tests**: `src/type_system/tests/` — test files organized by feature (e.g., `cancellation.rs`, `given_classes.rs`, `subtyping/`)
- **Interpreter tests**: `src/interpreter/tests/` — test files organized by feature (e.g., `array.rs`, `place_ops.rs`, `share.rs`)

Both use `expect_test` for snapshot testing. Type system tests use `assert_ok!`/`assert_err!`. Interpreter tests use `assert_interpret!`/`assert_interpret_only!`/`assert_interpret_fault!`.

## Documentation

- `book/` — mdBook documentation on the type system. Build with `mdbook build book/`.
- `md/wip/` — working design documents for in-progress features.

## formality-core Gotchas

Things that cause confusing errors if you don't know about them:

- **KEYWORDS reservation**: Adding a word to the KEYWORDS list in `declare_language!` (in `src/lib.rs`) prevents it from being used as an identifier anywhere. Grammar keywords (`#[grammar(x)]` on enum variants) work without being in KEYWORDS. Only add to KEYWORDS when you want to block identifier use.
- **Parser ambiguity**: Two `#[term]` enums with variants resolving to the same keyword in the same parsing context cause a runtime panic ("ambiguous parse"). Fix with `#[grammar(distinct_keyword)]`.
- **Prefix ambiguity**: If one variant's keyword is a prefix of another's in the same enum (e.g., `given` vs `given[x]`), the parser silently matches the shorter one. Use a distinct keyword (e.g., `given_from`).
- **Arc clone in judgment_fn**: Fields declared as `Arc<T>` become `&Arc<T>` in judgment rules. `.clone()` gives `Arc<T>`, not `T`. Use `T::clone(x)` for deref coercion to get `T`.
- **`for_all` vs `in`**: `(x in collection)` is existential (there exists). `for_all(x in coll) with(acc)` is universal (for all).
