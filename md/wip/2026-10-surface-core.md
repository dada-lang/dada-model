# Surface and core syntax implementation plan

Status: proposed October 11, 2026. No implementation steps are complete.

Introduce separate surface and core grammars. Surface judgments elaborate programs
into explicit core programs; core judgments check types and the interpreter executes
core programs. This plan records the agreed syntax and proposes an implementation,
including permission inference at calls. Update the checklist and implementation
notes in each implementing commit.

## Agreed syntax

Both languages use the same concrete permission vocabulary:

| Spelling | Meaning |
| --- | --- |
| `^` or `^[]` | Independent unique ownership |
| `^[x, y]` | Moved permission tracking its origins; properties depend on those origins |
| `shared` or `shared[]` | Independent shared ownership |
| `shared[x, y]` | Shared permission dependent on the listed origins |
| `![x, y]` | Mutable borrow dependent on the listed origins |

The empty-origin cases are semantic identities, not empty sets of possible
reductions: normalize `^[]` to unique ownership and `shared[]` to shared ownership.
Nonempty `^[...]` retains the current `given_from[...]` semantics; it does not
necessarily describe a unique value. Reject `![]`: mutable borrowing requires an
origin. Bare `!` is not an abbreviation for an empty mutable borrow.

The following conveniences belong to surface syntax:

| Surface type | Parameter lowering | Field or return lowering |
| --- | --- | --- |
| `String` | Fresh `P String`, binding `perm P` | `^String` |
| `any String` | Fresh `P String`, binding `perm P` | Not initially supported |
| `!String` | Fresh `P String`, binding `perm P`, predicate `P is mut` | Not initially supported |
| `^String` | `^String` | `^String` |
| `[x, y] String` | `shared[x, y] String` | `shared[x, y] String` |
| `[] String` | `shared String` | `shared String` |
| Explicit permission, e.g. `Q String` or `![x] String` | Preserve it | Preserve it |

Each sugared parameter introduces an independent permission variable. Explicit
variables allow parameters to share a permission. The proposed initial scope is
outermost parameter permissions; do not recursively turn `Array[String]` into
`P Array[Q String]`. Nested bare types retain core ownership defaults. Bare type
variables in parameter position follow the same outermost rule. Keep receivers
explicit initially; changing receiver defaults is a separate decision.

### Place expressions and dropping

The new access spellings apply in both surface and core syntax:

| New spelling | Existing operation |
| --- | --- |
| `place^` | `place.give`: give or move the value |
| `place!` | `place.mut`: mutably borrow the place |
| `place` | Share the place, yielding `shared[place]` (formerly `place.ref`) |
| `place.share` | Explicit place sharing, yielding `shared[place]` |
| `place^.share` | `place.give.share`: give the value and share it |
| `drop place;` | Drop the place as a statement, without producing a value |

There is one sharing concept, with distinct operations on places and values.
Sharing a place yields `shared[place]`; sharing a value yields `shared[]`.
Thus `place^.share` gives the value and then shares that value with an empty origin
list. Preserve this distinction in the AST and lowering judgments: do not elaborate
the operand of `place.share` as an implicit place share followed by value sharing.
Value sharing still requires the appropriate shareability checks. An empty outer
permission origin list does not erase dependencies carried inside the value's type;
test those dependencies separately from the sharing operation's origin list.

Remove `ref` as a language/model concept, not merely as a parser spelling. Use
place sharing and value sharing in the grammar, judgments, diagnostics, and book.
References to the old vocabulary in this plan describe migration inputs only.

Keep `Place` itself free of access operations: an assignment destination and the
operand of `drop` designate storage, while a bare place in value position performs
shared access. Lower `drop place;` directly to a drop statement/core operation,
without first borrowing or moving the operand. Reject it in value positions such
as `let x = drop place;`. Retain the existing drop checks and interpreter cleanup.
Class destructor syntax `drop { ... }` remains distinct and unchanged.

The core AST can retain internal access variants such as `Access::Mt`; source syntax
need not match Rust variant names. Rename internal `Rf`/`Ref` operations and shared
permission variants to express place sharing and value sharing as part of the
migration. Runtime reference counting remains; implementation distinctions between
handles with and without ownership do not introduce a separate `ref` concept.

No concrete permission is spelled `given`, `given_from`, `ref`, or `mut` in the
finished grammar. `mut` remains the predicate used by `P is mut`. The request to
remove the `given` keyword also affects `given class` and `P is given`; proposed
spellings are `^ class` and `P is ^`, subject to confirmation before that migration.
Remove the old `.give`, `.mut`, `.ref`, and `.drop` spellings after migrating their
uses. Preserve `.share` with the place-versus-value distinction described above.

## Current implementation constraints

- `src/grammar.rs` defines the AST with formality-core `#[term]` parsers.
  `src/lib.rs` and `src/test_util.rs` parse directly into `Program` and check it.
- `MethodDecl` contains a binder around receiver, inputs, output, predicates, and
  body. The custom method parser currently supplies the unit return default.
- `src/grammar/ty_impls.rs` treats a bare core type as uniquely owned.
- `resolve_method` in `src/type_system/expressions.rs` instantiates a method binder
  with explicitly supplied arguments. There is no existing permission inference
  solver to enable by inserting existential variables.
- Call checking evaluates the receiver and arguments in order, tracks their
  temporary places, proves predicates, normalizes the result before popping the
  temporaries, and checks drops. Elaboration must preserve this behavior.
- All declarations are currently classes with methods and explicit receivers.
  Examples written as standalone functions illustrate signature syntax; adding
  free functions is outside this plan.

## Module and language boundary

Proposed layout:

```text
src/core/mod.rs
src/core/grammar.rs + grammar/
src/core/type_system.rs + type_system/
src/core/interpreter/mod.rs + interpreter/
src/surface/mod.rs
src/surface/grammar.rs + grammar/
src/surface/desugar.rs + desugar/
```

Move the current implementation under `core` mechanically before changing behavior.
Use separate Rust AST types for surface declarations, types, and expressions; core
must not accept surface holes or depend on surface modules. Share identifier and
binding infrastructure where practical. Prototype formality-core binder/fold/cast
integration first: two ASTs do not necessarily require two `declare_language!`
instances. Choose the simplest working infrastructure without conflating the ASTs.

Surface lowering uses `judgment_fn!` rules, including explicit context for parameter
versus field/return defaults. Rust helpers may implement fresh-name generation,
binder construction, and bookkeeping; semantic choices belong in judgments.
Conceptual interfaces are:

```text
lower_parameter_type(surface_ty) => (core_ty, new_bindings, predicates)
lower_value_type(surface_ty) => core_ty
lower_signature(surface_method) => (core_signature, implicit_parameter_map)
elaborate_expr(signatures, env, live_after, surface_expr)
    => (core_expr, updated_env, core_ty)
elaborate_program(surface_program) => core_program
```

The program judgment first lowers all signatures, then elaborates bodies against
that signature table. Forward calls and recursive methods therefore see the same
complete declarations. Rebuild binders using fresh variable identities, not invented
source names. Class parameters, explicit method parameters, and generated method
parameters must remain correctly scoped through opening and rebinding.

Keep generated variables and their input positions in a surface-side signature map.
Append them to explicit method binders in source parameter order. Surface call
brackets supply only explicitly declared generics; core call brackets supply every
generic argument in binder order. The final core program needs no inference metadata.

## Inferring implicit permission arguments at calls

Use typed elaboration, not textual desugaring. The proposed first implementation
infers only the fresh outermost permissions introduced by bare types, `any`, and
`!`. Explicitly declared type and permission generics still require explicit call
arguments. General generic inference and coercion search are separate work.

For a signature schematically written as:

```text
surface: fn foo(x: !String, y: String)
core:    fn foo[perm P, perm Q](x: P String, y: Q String)
             where P is mut
```

infer `P` and `Q` independently from the actual argument types. A mutable borrow
`x!` can supply `![x]` to `P`; a uniquely owned argument does not satisfy `is mut`
merely because its fields are assignable. No implicit borrow or sharing conversion
is introduced by this plan. A surface call with explicit type arguments preserves
their order and appends the inferred permission arguments in the core call.

Implement the call judgment in these stages:

1. Elaborate the receiver, look up the lowered signature, and instantiate its
   explicit generics. Allocate surface-only inference slots for its generated
   permissions, with provenance pointing to the corresponding parameter.
2. Elaborate arguments left to right using the core call's liveness and temporary
   discipline. Synthesize each argument's type before checking it against its
   formal parameter. Extract its outer permission using the existing permission/type
   decomposition; use that permission as the candidate for the associated slot.
   Preserve compositions, origin sets, disjunctions, and permission variables.
3. Substitute candidates into the formals and check ordinary core subtyping and
   method predicates in the correct environment. Candidate extraction is not a
   proof of compatibility: named types, nested parameters, variance, and dependent
   places still require the existing judgments. An explicit expected type can guide
   an argument where available, but never invent a permission for an unresolved slot.
4. Emit the core call with a complete list of permission/type arguments. Reject
   unresolved slots with a diagnostic identifying the source parameter. For example,
   a context-dependent panic expression `!` cannot alone determine a fresh permission;
   ask for a typed argument or an explicitly permissioned signature. Do not silently
   default such a slot to `^` or choose a weaker permission to make a predicate pass.
5. Preserve result normalization, dependency checks, and temporary cleanup. Run the
   completed program through core checking independently before interpreting it.

This is a deliberately bounded inference algorithm: it selects the actual outer
permission rather than searching for all possible supertypes. It is sound only when
ordinary core validation succeeds; it may reject calls that a future solver could
accept. Document that limit and test it explicitly.

### Temporary places and emitted arguments

An inferred permission can contain places introduced while evaluating an argument,
including in-flight places and call temporaries. Copying such an internal type into
an ordinary source-position call argument can create an out-of-scope reference.
This is an implementation requirement, not a printable-name problem.

Factor the current call preparation/checking machinery into reusable core judgments
so elaboration and checking agree on place identities and evaluation order. First
support candidates whose origins are already expressible at the call. For candidates
that require argument temporaries, use a scoped core call representation with explicit
receiver/argument bindings and explicit generic arguments inside that scope. The
checker and interpreter must give those bindings the current call-temporary lifetime;
do not approximate it by ordinary source `let` statements and extra `^` accesses.
This representation contains no inference holes and can be checked independently.
Retain ordinary core calls as syntax lowering to the same preparation machinery.

Before fixing that AST shape, implement a small prototype covering a nested call,
a moved argument, and a returned borrow. Confirm that emitted permission arguments
remain in scope, interpretation evaluates each expression once, and return permissions
are normalized before the bindings disappear. This milestone must pass before
claiming general call-site support. Plain-place examples alone are insufficient.

## Permission representation and parser changes

Keep internal distinctions where they carry semantic or runtime information, but
express them in sharing vocabulary. Prefer a single shared permission family with
an origin set; if separate variants simplify the rules, name them for independent
sharing and place sharing. Existing `Rf`/`Ref` variants may be used during migration,
but must not remain as a separate concept in the completed model. Likewise `^[]`
constructs unique ownership rather than an empty moved-origin set. Add smart
constructors or well-formedness checks so programmatic construction cannot bypass
the empty-origin policy. Audit reduced permissions, predicate proving, normalization,
and interpreter dispatch for empty sets and avoid vacuous success.

Parse sigils with deliberate lookahead or custom parsing. The existing macro parser
has prefix pitfalls; do not rely on variant ordering to distinguish `^` from `^[...]`
or `shared` from `shared[...]`. Cover whitespace, projections, chained calls, and
postfix `x!` next to `!=`. Bare `!` remains the existing panic expression in expression
position; type-position `!T` and postfix access are separate productions. Specify
precedence so `x.field^` gives the projected place, `x^.share` shares the given
value, and `x.share` is the explicit shared place access. Test bare-place receivers
and method calls as well as projections; avoid ambiguity between a place projection
and the reserved `.share` operation. Cover `drop place;` separately from class
`drop { ... }`, and keep dropping out of value-expression grammar.

Canonical printing uses `^`, `shared`, and explicit nonempty origin lists. Surface
printing may use `[x] T`, but core printing uses `shared[x] T`. Core parsing retains
bare types as uniquely owned for existing tests; surface parameter defaults must
never leak into the core parser. Remove obsolete reserved keywords after migrating
all grammar uses, and test newly available identifiers.

## Implementation sequence

- [ ] Establish a clean baseline with `cargo test --all --workspace`; record results.
- [ ] Move grammar, typing judgments, and interpreter beneath `core` without semantic
  changes. Update imports, snippet extraction paths, and AGENTS.md in the same commit.
- [ ] Add surface ASTs and signature/type lowering judgments, fresh binders, and
  explicit context-dependent defaults. Cover multiple implicit parameters and
  collisions with explicit generics. Keep existing test macros targeting core.
- [ ] Implement concrete permission spellings and empty-origin rules in core and
  surface, plus all place-access spellings and statement-only dropping. Migrate
  model programs, snapshots, and
  documentation together. Resolve class/predicate spellings before removing `given`.
- [ ] Prototype scoped call elaboration and factor reusable call judgments. Verify
  origin scope, evaluation order, and cleanup against current explicit calls.
- [ ] Implement bounded permission inference and complete core-call emission, including
  explicit/implicit generic mapping, forward calls, recursion, and diagnostics.
- [ ] Add surface test entry points for parse/lower snapshots, type checking, and
  interpretation. Switch the normal CLI to surface input and provide an explicit
  core-input mode; interpreter-bypass core tests keep their existing purpose.
- [ ] Complete semantic regression coverage and update the book, source map, keyword
  documentation, and this plan's implementation record. Remove temporary migration
  aliases; the final grammar should have one canonical vocabulary.

## Validation and acceptance

Use parser snapshots for syntax and binder structure, and complete Dada programs
for semantic behavior. Put new semantic cases in property modules with authoritative
headers, while parser/tooling tests can live beside the grammars. Preserve existing
property IDs and snippet anchors where possible; module relocation must not silently
break mdBook extraction.

Required cases include:

- Parameter `T` and `any T` introduce fresh permissions; field/return `T` stays unique.
  Two implicit parameters are independent; explicit generics retain their scopes.
- `!T` requires `is mut`; pair mutable-lease acceptance with unique-owner and shared
  rejection. `![x] T` remains concrete. Reject `![]`, including internal construction.
- `^[]` and `shared[]` match their bare spellings. Nonempty moved origins preserve
  the current dependency, duplication, and predicate behavior. Place sharing
  retains its origin dependency; value sharing yields `shared[]` and retains
  ownership/refcount behavior. Check nested type dependencies independently.
- Inferred calls agree with equivalent fully explicit core calls for unique, shared,
  borrowed, moved, composed, disjunctive, and abstract permission arguments.
- Mixed explicit/implicit generics, multiple arguments, projections, nested calls,
  forward/recursive calls, and calls inside generic classes all lower correctly.
- Moves during later argument evaluation do not invalidate earlier inferred origins;
  returned borrows survive or are rejected according to core cleanup rules. Dropping
  arguments and sharing values produce the same interpreter results and heap state.
- Unresolved inference and wrong predicates report the relevant surface parameter.
  No inference slots or unbound temporary places survive into accepted core programs.
- Round-trip core parsing/printing covers new sigils, `!=`, panic `!`, and access
  chains. Bare `place` and `place.share` behave identically, including origin
  dependencies; `place^.share` yields `shared[]` through value sharing. Verify both
  resulting permissions explicitly as well as runtime behavior.
  Cover projected places, assignment destinations, method receivers, and move
  invalidation. `drop place;` performs cleanup without an intermediate access;
  reject dropping in value positions and preserve class destructor parsing.
  Old permission and access spellings are rejected after migration.

Run `cargo test --all --workspace` after each implementation milestone. Use
`UPDATE_EXPECT=1 cargo test --all --all-targets` only for intentional snapshot changes,
inspect the diffs, and rerun without snapshot updates. Run `mdbook build` after
source moves and documentation migration. Acceptance requires independent core
checking and successful interpretation of elaborated end-to-end cases, not just
matching lowering snapshots.

## Decisions to confirm during implementation

The syntax table and empty-origin semantics are agreed. Proposed implementation
choices still requiring review are the `^ class` / `is ^` spellings, outermost-only
parameter sugar (including type variables), explicit receivers, the scoped core-call
AST, and the deliberately bounded inference policy. Keep these distinctions visible
rather than treating a prototype's limitations as established language semantics.

## Implementation record

- October 11, 2026: plan written; implementation not started.
- October 11, 2026: incorporated postfix give/mutable access, implicit and explicit
  shared place access, give-then-share, and prefix drop statements.
- October 11, 2026: clarified that sharing replaces the `ref` concept throughout
  the model: place sharing yields `shared[place]`, value sharing yields `shared[]`.
