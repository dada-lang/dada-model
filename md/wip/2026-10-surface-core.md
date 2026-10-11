# Surface and core syntax implementation plan

Status: implementation started October 11, 2026. See phase checklist and record below.

Introduce separate surface and core grammars. Surface judgments elaborate programs
into explicit core programs; core judgments check types and the interpreter executes
core programs. This plan records the agreed syntax and proposes an implementation,
including explicit call arguments for automatically introduced permissions. Update the checklist and implementation
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
variables allow parameters to share a permission. Implicit parameter permission
defaults apply only at the outermost level, when the parameter type has no explicit
permission. Thus `Array[String]` becomes `P Array[^String]`, not
`P Array[Q String]`. Nested bare types retain core ownership defaults, and an
explicit outer permission suppresses the implicit default. Bare type variables in
parameter position follow the same outermost rule.

Receivers use the same parameter rules, with the enclosing declaration's type
supplied implicitly:

| Surface receiver | Core receiver | Generated constraint |
| --- | --- | --- |
| `self` or `any self` | `P self`, fresh `perm P` | None |
| `!self` | `P self`, fresh `perm P` | `P is mut` |
| `^self` | `^self` | None |
| `shared self` | `shared self` | None |
| Explicit `Q self` | `Q self` | None |

The receiver's generated permission is independent of those introduced by other
parameters. Callers supply its permission argument explicitly, just as for the
permissions introduced by other parameters. No call-site inference is planned.

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
finished grammar. `mut` remains the predicate used by `P is mut`. Remove the
standalone `is given` predicate; express its intended ownership category as the
conjunction of exclusivity and ownership, as described below.
Remove the old `.give`, `.mut`, `.ref`, and `.drop` spellings after migrating their
uses. Preserve `.share` with the place-versus-value distinction described above.

### Classes and structs

Use declaration keywords to distinguish the three categories, without a sigil on
the declaration or its name:

| New declaration | Current category | Meaning |
| --- | --- | --- |
| `class Foo` | `given class Foo` | Uniquely owned, affine data; may have a destructor |
| `struct Foo` | Plain `class Foo` (the share category) | Data that can be shared and has no destructor |
| `shared struct Foo` | `shared class Foo` | Always-copyable value data |

Plain `class` is the conservative default: sharing is an opt-in expressed by
declaring a `struct`. Preserve the existing category semantics, including field
mutation rules and restrictions on generic parameters. A class can still be
shared as a place; that does not convert its value to independent shared ownership.

Rename the `share` predicate to `struct`: `T is struct` means the existing
shareability property, including its checks on generic arguments. It includes
shared structs; it is not an exact test of the declaration's spelling. `.share`
remains the operation, and `shared` remains the predicate for duplicable values.
Carry the vocabulary change through Rust category/predicate names, judgments,
diagnostics, and documentation.

Migrate declarations by meaning: existing `given class` becomes `class`, existing
plain `class` becomes `struct`, and existing `shared class` becomes `shared struct`.
Do not silently reinterpret existing tests' plain classes under the new default.
The `^ class` and `class ^Foo` alternatives are not part of the planned syntax.

### Remove the given predicate

Rename the current `move` predicate to `unique`. The two predicates describing
duplication behavior are `unique` (moved rather than duplicated) and `shared`
(duplicable). Uniqueness includes both unique owners and mutable permissions;
`owned` is a separate property distinguishing independent ownership. Independent
unique ownership is expressed as `P is unique, P is owned`. Keep `mut`, `struct`,
and `boxed` for their separate properties. For abstract parameters, failure to
prove `shared` does not itself prove `unique`, or vice versa; retain explicit
proof requirements rather than treating either predicate as logical negation.
The discussion's `unique + owned` denotes conjunction, not a decision to add `+`
syntax to where clauses.

The existing `prove_is_given` helper already proves `move` and `owned`, and is used
by reduced-permission subtyping and permission-disjunction classification. Preserve
that conjunction where those algorithms need it, with an appropriately named helper.
The separate `ParameterPredicate::Given` has narrower rules for literal `given`
and disjunctions, plus generic assumptions. Remove that predicate and its grammar;
migrate its assumptions and tests to the conjunction rather than merely renaming
the variant. Check generic entailment and origin-derived permissions explicitly,
since the two existing proof paths are not interchangeable in every case today.

## Current implementation constraints

- `src/core/grammar.rs` defines the AST with formality-core `#[term]` parsers.
  `src/lib.rs` and `src/test_util.rs` parse directly into `Program` and check it.
- `MethodDecl` contains a binder around receiver, inputs, output, predicates, and
  body. The custom method parser currently supplies the unit return default.
- `src/core/grammar/ty_impls.rs` treats a bare core type as uniquely owned.
- `resolve_method` in `src/core/type_system/expressions.rs` instantiates a method binder
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
lower_method(surface_method) => core_method
lower_expr(surface_expr) => core_expr
lower_program(surface_program) => core_program
```

The program judgment lowers declarations and bodies structurally. Call lowering
preserves the caller's explicit generic arguments; it does not synthesize argument
types or solve permissions. Core checking handles name resolution, forward and
recursive calls, binder instantiation, predicates, and type compatibility after the
whole program has been lowered. Rebuild binders using fresh variable identities,
not invented source names. Class parameters, explicit method parameters, and
generated method parameters must remain correctly scoped through opening and rebinding.

Append automatically introduced permission parameters after all explicitly declared
method parameters, preserving the explicit parameters' original order. The
order within the generated suffix is receiver first, then other parameters from
left to right. A declaration with an explicit
permission introduces no additional slot for that input. Retain source provenance
for diagnostics explaining which input introduced each generated parameter; the
core checker needs only the complete binder.

## Explicit arguments for generated permissions

There is no type or permission inference in this implementation. Parameter sugar
introduces generic bindings in declarations; it does not make their instantiation
implicit at calls. Both surface and core callers must supply the full list of generic
arguments: explicitly declared parameters first, followed by generated permissions.
Do not insert holes, choose default permission arguments, or derive arguments from
the receiver or other expression types.

For example, with receiver-first ordering:

```text
surface: fn foo[ty T](!self, x: T, y: ^String)
core:    fn foo[ty T, perm R, perm P](R self, x: P T, y: ^String)
             where R is mut
```

A call supplies `[T_argument, R_argument, P_argument]`. The concrete `^String`
parameter contributes no generated permission. Existing explicit permission
parameters also keep their positions before the generated suffix. Automatically
introduced variables need not have user-visible names: their positions determine
which call arguments instantiate them.

Lower call expressions and their explicit generic arguments with the ordinary
surface judgments, then use existing core instantiation and checking. Report missing,
extra, or wrong-kind generic arguments with the fully expanded signature and generated
parameter provenance. Prove the generated predicates normally: an argument for `!self`
must satisfy `is mut`; unique ownership alone does not meet that condition. Check
in-scope explicit origins using the existing core rules.

Keep the current core call representation and temporary lifetime behavior. The
previously proposed typed call elaborator, inference slots, scoped-call AST, and
inference-specific temporary-scope prototype are outside this plan. No new caller
bindings or extra accesses should be inserted just to lower parameter sugar. Preserve
receiver/argument evaluation order, predicate checking, return normalization, and
temporary cleanup through the existing checker and interpreter. Broader generic
inference can be designed separately if requested later.

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
printing may use `[x] T`, but core printing uses `shared[x] T`. Core programs are
expressible as an explicit subset of surface syntax: print parameter and receiver
permissions explicitly so reparsing through surface does not introduce fresh
parameters. In particular, print a uniquely owned core parameter as `^T`, not bare
`T`. Remove obsolete reserved keywords after migrating all grammar uses, and test
newly available identifiers.

## One surface entry point for program tests

All program assertion macros start with surface syntax. Keep the familiar macro
names; change their shared parsing helpers to lower into core before checking or
interpreting:

| Macros | Pipeline |
| --- | --- |
| `assert_ok!`, `assert_err!` | Parse surface, lower, core type-check |
| `assert_interpret!` | Parse surface, lower, core type-check, interpret core |
| `assert_interpret_only!`, `assert_interpret_fault!` | Parse surface, lower, interpret core without type-checking |

The interpreter-only/fault helpers bypass checking, not surface parsing or lowering.
Preserve their ability to exercise type-incorrect programs that lower successfully.
Keep parse/lowering failures distinct from type errors and expected runtime faults.

Do not keep a separate core-input program-test suite or add parallel `assert_core_*`
macros. Programs using the explicit core subset go through the same surface entry
point, exercising lowering even when there is little sugar to remove. Parser and
lowering tests may inspect core ASTs, and existing focused judgment tests may still
construct terms directly; these do not require a second program input language.

Migrate existing programs by meaning. Bare parameter types that currently mean
unique ownership become `^T`, and explicitly permissioned receivers stay explicit.
Preserve explicit generic calls without accidentally adding generated parameters.
Migrate each declaration or access spelling with its corresponding implementation
phase, and add dedicated cases that intentionally exercise the new defaults. Normal CLI input
also follows the surface pipeline; a separate core-input mode is not required.

## Implementation phases with passing tests

Every phase ends with `cargo test --all --workspace` passing. Keep each phase in a
reviewable commit, or several independently passing commits if needed. Update tests,
snapshots, affected book prose, AGENTS.md, and this plan in the same implementing
commit. Do not defer test migration or documentation to a final cleanup, disable
failing tests, or change expected acceptance merely to accommodate an intermediate
state. A deliberate semantic change gets an explicit regression case and explanation.

The key boundary is phase 2: all program tests enter through surface before any
syntax or default changes. Initially the two grammars accept the same language and
lowering preserves its meaning. Only later phases introduce differences.

- [x] **0. Record the baseline.** Run the workspace tests and record their results.
  Establish the current book build result so later source moves have a comparison.
- [x] **1. Isolate core mechanically.** Move grammar, typing judgments, and interpreter
  beneath `core`, without changing accepted syntax or semantics. Repair imports and
  book extraction paths. This phase leaves existing test inputs unchanged.
- [x] **2. Add an identical surface grammar and switch all program tests.** Introduce
  distinct surface ASTs and structural lowering judgments, preserving current syntax,
  defaults, binder order, and meaning. Route every existing assertion helper and the
  normal CLI through parse-surface/lower-to-core. Interpreter-only/fault helpers lower
  but still bypass checking. All existing program text remains unchanged. Verify the
  full existing suite through this path, plus focused lowering/binder snapshots;
  do not proceed with syntax changes until this phase passes. No permanent parallel
  core-input assertion path is introduced.
- [x] **3. Spell owned permissions with `^`.** Replace permission `given` with `^`
  and `given_from[...]` with `^[...]` in both grammars. Implement `^[] = ^` and
  canonical printing. Migrate permission occurrences in tests and documentation;
  leave the still-existing class and predicate uses of `given` for their own phases.
- [x] **4. Spell mutable permissions with `![...]`.** Replace permission `mut[...]`
  in both grammars and migrate tests. Reject `![]` with explicit negative coverage.
  Keep the `mut` predicate and old mutable place access until its separate phase;
  bare type-position `!T` does not exist yet.
- [x] **5. Unify shared permission vocabulary.** Replace permission `ref[...]` with
  `shared[...]`, implement `shared[] = shared`, and migrate corresponding internal
  permission names, rules, tests, and prose. Preserve origin-dependent and independent
  sharing behavior. Place-access spelling changes happen in phase 8.
- [x] **6. Change give access to postfix `^`.** Replace `place.give` with `place^`
  and migrate all uses, including give-then-share expressions. Cover projections,
  precedence, and chained calls through the surface pipeline.
- [x] **7. Change mutable access to postfix `!`.** Replace `place.mut` with `place!`
  and migrate tests. Cover interactions with panic `!`, `!=`, and chained calls.
- [x] **8. Introduce implicit and explicit place sharing.** Replace `place.ref`
  with bare `place` or `place.share`; retain value sharing as a distinct operation,
  including `place^.share`. Audit existing `.share` operands so each test retains
  its intended place-sharing or value-sharing operation, rather than merely passing
  under a different interpretation. Migrate access variants and runtime terminology so `ref`
  is no longer a separate model concept. Test projections, receivers, origins, and
  sharing results. Assignment destinations remain places, not implicit accesses.
- [x] **9. Make dropping a statement.** Replace `place.drop` with `drop place;`
  in both grammars and migrate tests. Preserve cleanup and destructor execution;
  add rejection cases for drop in value position and parsing cases for `drop { ... }`.
- [x] **10. Introduce class and struct declaration names.** Migrate old `given class`
  to `class`, old plain `class` to `struct`, and old `shared class` to `shared struct`
  atomically with the grammar/default change. Preserve each existing test's category;
  do not apply sequential textual replacements that reclassify already-migrated
  declarations. Cover destructors, sharing, and generic restrictions under the new names.
- [x] **11. Rename the shareability predicate.** Replace `is share` with `is struct`
  throughout syntax, judgments, tests, and diagnostics, preserving its existing rules.
- [x] **12. Rename the duplication predicate.** Replace `is move` with `is unique`
  throughout syntax, judgments, tests, and diagnostics, preserving its existing rules.
- [ ] **13. Remove the standalone given predicate.** Migrate `is given` constraints
  to `is unique, is owned`; retain a conjunction helper where core algorithms need
  one. Test abstract assumptions, moved origins, subtyping, and disjunction categories.
  Remove `given` from the reserved keywords once no grammar use remains.
- [ ] **14. Add surface type conveniences.** Add `[places] T` as surface sugar for
  `shared[places] T`, including `[] T`. Add explicit `any T` and `!T` parameter sugar,
  including `any self` and `!self`, with fresh binders and constraints. Generated
  permissions follow explicit generics, receiver first then left to right. Calls
  supply every argument explicitly. Existing bare parameter defaults are still
  unchanged; exercise the new sugar in dedicated passing/rejecting cases, including
  arity, kind, ordering, and binder hygiene. No inference is added.
- [ ] **15. Change surface parameter defaults.** Make an outermost parameter type
  without a permission mean `any T`, and bare `self` mean `any self`. In this same
  phase, migrate existing bare parameters that must retain ownership to `^T`; keep
  explicit permissions and existing generic call arities unchanged. Add intentional
  new-default tests supplying the generated arguments at calls. Field, return, and
  nested type defaults stay owned. Core printing must use explicit permissions so
  printed core programs can pass through surface without generating new binders.
- [ ] **16. Verify completion.** Run the full suite and book build, check surface/core
  round trips and all assertion paths, and confirm obsolete spellings are rejected.
  Audit source maps, keyword lists, property prose, and snippet links for omissions;
  routine updates should already have landed with their corresponding phases.

Temporary old spellings may remain only until their specific migration phase; each
completed spelling change removes its obsolete alias and updates its tests. Syntax
in both grammars changes together where intended. Final surface-only sugar never
becomes an inference hole or an unchecked shortcut in core.

## Validation and acceptance

Use parser snapshots for syntax and binder structure, and complete Dada programs
for semantic behavior. Put new semantic cases in property modules with authoritative
headers, while parser/tooling tests can live beside the grammars. Preserve existing
property IDs and snippet anchors where possible; module relocation must not silently
break mdBook extraction.

Required cases include:

- Parameter `T` and `any T` introduce fresh permissions; field/return `T` stays unique.
  Two implicit parameters are independent; explicit generics retain their scopes.
- Receivers follow the same defaults and constraint generation as other parameters.
  Test `self`, `!self`, `^self`, and `shared self`, their explicit trailing call arguments,
  and independence of generated receiver/input permissions. Bare place receivers
  share the place; mutable or owned receiver requirements need suitable expressions.
- Class/struct migration preserves category behavior: classes permit destructors,
  structs permit value sharing but no destructor, and shared structs remain
  duplicable. `is struct` retains the previous shareability predicate's generic
  restrictions. Place sharing of class values remains possible under its usual
  dependency checks.
- Independent unique ownership is proved from both exclusivity and ownership,
  including generic assumptions and moved origins. Mutable permissions satisfy
  exclusivity without ownership; independent shared permissions satisfy ownership
  without exclusivity. Remove the old `is given` grammar and test disjunction
  classification and subtyping through the conjunction.
- `!T` requires `is mut`; pair mutable-lease acceptance with unique-owner and shared
  rejection. `![x] T` remains concrete. Reject `![]`, including internal construction.
- `^[]` and `shared[]` match their bare spellings. Nonempty moved origins preserve
  the current dependency, duplication, and predicate behavior. Place sharing
  retains its origin dependency; value sharing yields `shared[]` and retains
  ownership/refcount behavior. Check nested type dependencies independently.
- Surface calls with complete explicit generic arguments agree with the lowered
  core calls for unique, shared, moved, mutable, composed, disjunctive, and abstract
  permissions. No generic argument is inferred, including generated permissions.
- Explicitly declared generics precede generated permissions; inputs with explicit
  permissions introduce no extra slots. Check ordering with multiple inputs and a
  sugared receiver, plus missing, extra, and wrong-kind argument rejection.
- Multiple arguments, projections, nested calls, forward/recursive calls, and calls
  inside generic classes all lower correctly.
- Moves during later argument evaluation and returned shared/mutable values retain
  existing core dependency and cleanup checks. Dropping arguments and sharing
  values produce the same interpreter results and heap state.
- Wrong predicates and generic-argument errors identify the relevant surface input.
  Sugar lowering introduces no caller temporaries or out-of-scope origins.
- Round-trip surface parsing and core lowering/printing covers new sigils, `!=`, panic `!`, and access
  chains. Bare `place` and `place.share` behave identically, including origin
  dependencies; `place^.share` yields `shared[]` through value sharing. Verify both
  resulting permissions explicitly as well as runtime behavior.
  Cover projected places, assignment destinations, method receivers, and move
  invalidation. `drop place;` performs cleanup without an intermediate access;
  reject dropping in value positions and preserve class destructor parsing.
  Old permission and access spellings are rejected after migration.
- All program assertion macros, including interpreter-only/fault variants, use the
  surface pipeline. Printing a lowered core program and parsing/lowering it again
  preserves its meaning and binder structure modulo fresh variable identities;
  explicit core parameters do not acquire additional generated permissions.

Run `cargo test --all --workspace` after each implementation milestone. Use
`UPDATE_EXPECT=1 cargo test --all --all-targets` only for intentional snapshot changes,
inspect the diffs, and rerun without snapshot updates. Run `mdbook build` after
source moves and documentation migration. Acceptance requires core checking and
successful interpretation through the surface pipeline for checked end-to-end
cases, not just matching lowering snapshots. Interpreter-only/fault tests retain
their deliberate checking bypass.

## Agreed implementation scope

The syntax tables, declaration categories, `is struct` predicate, empty-origin
semantics, removal of `is given`, renaming `move` to `unique`, outermost-only defaults,
and consistent receiver defaults are agreed. There is no inference in the initial
implementation. Generated permission parameters come after all explicit parameters,
with the receiver first, followed by other generated permissions in source order.
Every program assertion macro starts from surface syntax and lowers to core; there
is no separate core-input program-test suite.
The earlier scoped-call representation and bounded inference proposal are no longer
part of this implementation.

Inference remains a desirable future extension. Preserve the association between
generated parameters and their source inputs; the trailing generated suffix could
then be omitted at calls if a later inference design allows it. Selecting permissions
through subtyping and keeping their origins in scope require a separate design;
this extension is not an acceptance requirement for the initial implementation.

## Implementation record

- October 11, 2026: plan written; implementation not started.
- October 11, 2026: incorporated postfix give/mutable access, implicit and explicit
  shared place access, give-then-share, and prefix drop statements.
- October 11, 2026: clarified that sharing replaces the `ref` concept throughout
  the model: place sharing yields `shared[place]`, value sharing yields `shared[]`.
- October 11, 2026: chose `class`, `struct`, and `shared struct` for the declaration
  categories, with `is struct` replacing `is share`. The ownership predicate's
  replacement spelling remains open.
- October 11, 2026: chose to remove `is given` and express independent unique
  ownership as exclusivity plus ownership. Whether `unique` replaces the current
  `move` predicate name remains open.
- October 11, 2026: confirmed `unique` replaces `move`, paired with `shared` for
  duplication behavior. Ownership and the other predicate properties remain separate.
- October 11, 2026: confirmed implicit parameter permission defaults apply only to
  an outermost type without an explicit permission; nested types keep ownership
  defaults.
- October 11, 2026: confirmed receivers follow the same parameter rules, including
  fresh permission generation and `!self` constraints. The initial call-inference
  proposal was superseded by the explicit-argument decision below.
- October 11, 2026: clarified that no inference is expected. Generated permission
  parameters follow all explicit generics, and calls supply their arguments explicitly.
  Removed typed call elaboration and the scoped-call AST from the implementation scope.
- October 11, 2026: confirmed receiver-first, left-to-right ordering within the
  generated suffix. Inference remains desirable future work, outside the initial scope.
- October 11, 2026: all program assertion macros will parse surface and lower to
  core, including interpreter-only/fault tests. Existing semantic tests migrate
  with explicit permissions rather than retaining a separate core-input suite.
- October 11, 2026: reorganized implementation into independently passing phases.
  An initially identical surface grammar takes over every program-test entry point
  before syntax changes; individual spelling migrations follow, and implicit
  parameter defaults change last with meaning-preserving test edits.

- October 11, 2026, phase 0: baseline passed (815 model tests, 11 preprocessor tests).
  `mdbook` was absent from PATH; book tooling setup is being checked independently.
- October 11, 2026, phase 1: moved grammar, typing, and interpretation beneath
  `core`; root re-exports preserve Rust API paths. Updated documented source links.
- October 11, 2026: installed temporary mdBook 0.5.2/mermaid tooling under
  `/private/tmp/dada-book-tools`; baseline book builds. Existing warning: obsolete
  `ref|mut place` rule link, to be repaired with place-sharing documentation.
- October 11, 2026, phase 2: distinct surface ASTs and structural judgment lowering
  now feed the CLI and every assertion helper. Unchanged programs pass: 820 model
  tests (five new lowering checks), 11 preprocessor tests; book builds. No snapshot
  updates were required. Concrete permissions, places, and binding infrastructure
  are shared; type/expression/declaration ASTs are separate.
- October 11, 2026, phase 3: permissions now parse/print `^` and `^[...]`;
  `^[]` canonicalizes to independent ownership. A single prefix parse branch
  avoids ambiguity. Migrated program inputs, snapshots, and book vocabulary;
  824 model and 11 preprocessor tests pass. Class/predicate `given` remains for
  its later phases.
- October 11, 2026, phase 4: concrete mutable permissions use `![...]`; empty
  origins and legacy spelling are rejected by parser coverage. Updated programs
  and snapshots; 825 model and 11 preprocessor tests pass, and the book builds.
- October 11, 2026, phase 5: shared permissions use `shared[origins]`; empty
  origins normalize to independent `Shared`, with nonempty `SharedFrom` retained
  internally for existing rules. Added a canonicalizing constructor and rejected
  empty internal origin-only permissions in well-formedness. New end-to-end
  property tests distinguish owned/duplicable sharing from exclusivity. Four parser
  snapshots intentionally changed for empty-origin normalization. Verified without
  snapshot updates: 828 model tests and 11 preprocessor tests pass; book builds.
- October 11, 2026, phase 6: give access is postfix `^`, including projections
  and give-then-share/call chains. The full migrated suite passes unchanged in
  behavior: 828 model tests and 11 preprocessor tests.
- October 11, 2026, phase 7: mutable place access is postfix `!`. Existing
  mutation, projection, interpreter, and call cases pass after spelling migration:
  828 model and 11 preprocessor tests.
- October 11, 2026, phase 8: bare places and `.share` share from a place;
  value sharing remains a separate expression. Added projection/call/operator
  lookahead coverage and semantic origin/ownership checks. Renamed access, lien,
  reduced-link, and runtime variants to sharing/lease vocabulary. Existing
  acceptance and rejection outcomes are unchanged; snapshots reflect vocabulary.
  Verified 837 model tests, 11 preprocessor tests, and a complete book build.
- October 11, 2026, phase 9: added `Statement::Drop` to both ASTs, lowering,
  liveness, checking, and interpretation; `.drop` no longer parses as an access.
  Internal drop access checking is preserved, including retiring in-flight
  origins. Parser rejection and end-to-end last-use/destructor property tests
  supplement the migrated cases. Verified 840 model and 11 preprocessor tests.
- October 11, 2026, phase 10: declaration categories now spell `class`, `struct`,
  and `shared struct`, with Rust variants `Class`, `Struct`, and `Shared`. All
  existing declarations migrated simultaneously to preserve their category.
  The agreed no-destructor rule required tightening the old model: nonempty
  struct drop bodies are now rejected. Valid destructor examples use classes;
  interpreter-only shared-destructor examples remain explicitly unchecked.
  `drop {}` is indistinguishable from no body and remains accepted. Added the
  `only_classes_have_destructors` property. Verified 843 model tests, 11 book
  preprocessor tests, and the book build.
- October 11, 2026, phase 11: renamed the shareability predicate to `struct`,
  including constructors, proving judgments, program inputs, and book rule links.
  The operation `.share` is unchanged. Verified 843 model and 11 preprocessor
  tests without snapshot updates after the vocabulary migration.
- October 11, 2026, phase 12: renamed the exclusivity predicate and proving
  helpers from `move` to `unique`, reserving `unique` instead of `move`. Movement
  operations retain their meaning. Renamed the origin property and its includes.
  Verified 843 model tests and 11 preprocessor tests.
