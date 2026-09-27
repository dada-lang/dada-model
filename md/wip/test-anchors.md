# Draft: organize tests around semantic anchors

Status: initial survey September 23, 2026; first property extraction implemented
September 25, 2026. The survey below records the original layout and candidate
groupings, not newly accepted language policy. See the implementation record below
for the changes since the survey.

Inspired by [Principles of Anchor Engineering](https://nappingtoheavymetal.com/post/2026-09-15-principles-of-anchor-engineering/):
record the design judgments that should survive implementation changes, together
with the means of verifying them. The module organization below is our proposed
application of that principle.

Vocabulary update: the former `copy` predicate is now `shared`; the former
narrower `shared` is expressed as `shared` plus `owned`. Any shared permission
can be duplicated. One valid partial-drop test now also runs the type checker;
the broader interpreter-bypass audit remains pending.

## Scope and confidence

Source inventory (updated September 25): 627 `#[test]` declarations under `src`, plus 7 in
`mdbook-judgment`. Counts are declarations, not assertions or generated scenarios;
the Liskov matrix tests exercise many scenarios per test. The September 25 workspace run passed all 634 tests; the original
classification was based on source inspection. Inspected names, module introductions, comments, assertion
modes, and selected test bodies. This is a suite-wide first-pass grouping with
closer inspection of the examples below, not a semantic audit of every assertion.

Tests are evidence for particular cases of a claim, not a proof of its universal
truth. A green suite must not imply that all accepted anchors are implemented.

## Proposed organization

Use one primary semantic home per test, with cross-references to other claims it
exercises. An anchor should state a falsifiable proposition; a topic such as
"borrowing" is only a parent module containing several anchors.

For example (proposed paths, not existing files):

```text
src/anchors/
  mod.rs
  moves_preserve_dependencies/
    mod.rs                # claim, rationale, scope, secondary links
    checker.rs
    runtime.rs
    known_gaps.rs
  predicates_hold_for_every_source.rs
  call_returns_preserve_dependencies/
    mod.rs
    checker.rs
    runtime.rs
  destruction/
    scope_cleanup.rs
    partial_values.rs
    stored_reference_drop.rs
  examples/
    vec.rs
    lock_guard.rs
```

A crate-level `#[cfg(test)] mod anchors` can collect public/crate-visible test
APIs. Helpers requiring module-private access can stay next to their implementation
and explicitly name their anchor; decide visibility changes only during migration.
The existing direct tests inside `pop_normalize.rs` need this consideration.

Module documentation should contain:

- **Claim:** what must remain true, including relevant preconditions.
- **Reason:** why the language/model needs it.
- **Decision status:** candidate, accepted, or superseded, with a decision link.
- **Evidence and gaps:** checker acceptance/rejection, runtime behavior, unchecked
  runtime behavior, or a known counterexample. These are separate from decision status.
- **Scope of assertions:** what is semantically significant versus incidental in snapshots.

The book can include this claim text and selected examples using the existing
source-anchor machinery. Keep one authoritative claim statement; the book adds
explanation. Stable claim IDs and snippet IDs serve different purposes.

An explanatory test can still affiliate with anchors. Vec and lock-guard examples
are valuable integration evidence; "explanatory" describes their role, not an
exemption from explaining why they exist. Small arithmetic/parser/tooling tests
can protect model-infrastructure contracts without pretending to be ownership laws.

## Candidate anchor families

Each row may require several leaf modules; these are not proposed giant modules
with a single vague claim. Existing behavior is evidence to review, not authority.

| Family | Candidate leaf claims | Main existing evidence |
|---|---|---|
| Moves and copies | Giving a noncopy value consumes its source; moving a field preserves unaffected siblings; copyable values support repeated give | `move_check`, `copy_move`, parts of `place_ops`, `generics`, `mdbook` |
| Moves preserve dependencies | A transferred referent's dependent types track its destination; conflicts remain enforced at the new place | all five `move_tracking` tests; self-reference reconstruction tests |
| Borrow access | A live shared borrow excludes conflicting mutation; a live mutable borrow excludes conflicting access; disjoint access remains possible; dependencies propagate transitively | `permission_check`, borrowing examples in `mdbook`, `assignment` |
| Permission-aware field access | Reading through a permission respects that permission; writing requires mutation authority and the declared stored field type | `assignment`, field tests in `permission_check`, `place_ops`, `copy_move` |
| Cancellation | Dead intermediary borrows may cancel only under the permitted composition rules; every relevant place must be dead; subtyping preserves future cancellation behavior | `cancellation`, `subtyping/liskov/cancellation`, liveness examples, loan-kill tests |
| Predicates hold for every source | A predicate on a permission with multiple possible sources must hold for every source | all seven `predicate_quantifiers` tests; `predicate_or_*` |
| Permission alternatives | `or` branches share a representation category; every source alternative must be admitted by the target; every possible borrow contributes restrictions | `or_perm` split into well-formedness, subtyping, predicate, and access sections |
| Permission subtyping | Permission conversion preserves justified access and dependencies; source-place sets can widen but cannot arbitrarily narrow; composition order matters | `subpermission`, `subtyping`, Liskov matrices and subpermission cases, book examples |
| Generic permissions and variance | Generic operations require sufficient assumptions; relative/atomic positions constrain permitted substitutions | `class_defn_wf`, `variance_subtyping`, generic/subtyping cases |
| Class capabilities | Given classes cannot be shared; storage restrictions preserve their capabilities; copyability and permission erasure of shared-class instantiations depend on their arguments | `given_classes`, `shared_classes_*`, `subtyping/copy_types`, `class_defn_wf/shared_vs_share` |
| Dependent construction | Stored dependencies match the declared field relationships; dependencies survive supported assembly/disassembly; earlier initializer values remain protected | `new_with_self_references`; S1 in the soundness assessment identifies missing coverage |
| Calls preserve dependencies | Calls instantiate dependent signatures correctly; return permissions resolve before callee bindings disappear; returned borrows retain surviving referents | `fn_calls`, both `normalization` modules, `pop_normalize` unit tests |
| Scope and destruction | Scope exit cleans up locals in reverse order, including break; partial cleanup does not run a whole-value destructor; explicit drop destroys owned storage, including a stored borrow | `block_scoped_drops`, `drop_body`, `place_ops`; S2–S4 identify gaps and changed intent |
| Sharing and lifetime accounting | Shared-handle duplication retains backing storage; releasing a handle decrements its ownership count; borrowed handles do not run owning destructors | `share`, shared/refcount cases in `array`, `drop_body`, `place_ops` |
| Unsafe array contract | Array primitives check declared types/permissions; runtime access respects bounds and initialization; element ownership follows the requested permission; callers manage element destruction | `array_ops`, `array`, Vec examples; distinguish checker contract from unchecked runtime obligations |
| Representation | `size_of` and field/element addressing agree with the chosen word layout; mutable references reach the correct flat or boxed storage | `size_of`, mutable-reference `place_ops`, selected `array` and `vector` tests |
| Core evaluation and binding | Expressions produce expected scalar/control-flow results; method dispatch and parameter substitution preserve values; names, annotations and returns are checked | `basics`, `method_calls`, `type_check`, top-level checker tests, scalar cases currently in `drop_body` |
| Syntax and book tooling | Supported syntax parses to the intended terms; documentation extraction selects and renders the intended source fragments | `grammar/test_parse`; all seven preprocessor tests |

Avoid overclaiming "safe well-typed programs never fault" from the current suite:
there are known soundness failures and intentionally unchecked unsafe examples.
That can be an overarching objective, with explicit assumptions and known gaps,
but not a claim that these tests have established.

## Four concrete modules to start with

### `predicates_hold_for_every_source`

Claim: if a permission denotes a value from any of several sources, proving a
predicate requires it for every possible source.

Group the source-quantifier tests from `predicate_quantifiers.rs` together;
its two new vocabulary tests cover a separate shared/share/owned distinction. Their cases cover
all-shared, mixed shared/move in both orders, and mutation authority with uniform and
mixed sources. Add the `predicate_or_*` section of `or_perm.rs` as a submodule or
cross-reference. Check that mixed-category `or` tests actually reach predicate
proving: rejection for ill-formedness alone does not establish this claim.

### `moves_preserve_dependencies`

Claim: when a supported ownership transfer changes a referent's place, dependent
permissions follow that place, and continue restricting conflicting accesses.

All five `move_tracking.rs` tests belong here:

- `give_while_shared_then_use`: a dependent borrow survives transfer.
- `give_while_shared_then_drop`: dead dependents cease restricting the destination.
- `give_while_shared_then_move_while_shared`: discard of the destination conflicts with a later borrow use.
- `give_while_shared_then_assign_while_shared`: another transfer retargets the dependency again.
- `give_while_shared_then_assign_while_shared_then_mutate_new_place`: overwriting the new referent is rejected while needed.

`unpack_and_reconstruct_correct_order` is integration evidence linking this
anchor with dependent construction. Mutable references need special care: runtime
pointers may not survive relocation just because the checker renames a dependency.
Do not promote this into a universal "all borrows survive all moves" guarantee.

### `call_returns_preserve_dependencies`

The 20 checker normalization tests, 13 runtime normalization tests, and 2 local
`pop_normalize` tests provide an existing 35-test cluster. Leaf claims:

- Return permissions resolve into caller-valid terms before parameters are removed.
- Ownership may leave the call; a borrow of a destroyed owned argument may not.
- Static results conservatively retain possible alternatives.
- Runtime result types describe the branch actually returned.
- Callee bindings do not leak into the caller.
- Normalization does not erase a guard dependency merely because its binding dies.

The runtime helper checks result type and unchanged caller bindings directly;
these observations cannot be replaced by a display-only snapshot. Some tests
intentionally execute calls without checking those call expressions: label that
evidence accurately, even though the helper checks the shared class declarations.

### `guard_dependencies_survive_cancellation`

Claim: access obtained through a guard cannot escape by cancelling away the
obligation to keep that guard alive.

Pair `lock_guard_ok` and `lock_guard_cancellation`, with
`pop_normalize::tests::guard_link_cannot_be_stripped` linked as direct mechanism
evidence. The lock example could be owned here and included by the book, or live
in `examples` with this as its primary claim. Avoid duplicating its program solely
to serve both purposes.

## Cases that must not silently become accepted anchors

1. `new_with_self_references::choice_with_leased_self_ref_a` asserts acceptance,
   while its comment says it should fail (FIXME#12). Record as a counterexample
   pending confirmation of current intent, not support for safe relocation.
2. `unpack_and_reconstruct_wrong_order` explicitly says rejection occurs for a
   different reason than intended. The negative result is weaker evidence than
   the desired rule; make the eventual regression isolate that rule.
3. `shared_classes_permissions::mutate_field_of_our_class_applied_to_share` asks
   whether its accepted behavior is good. It is a design question, not settled policy.
4. `permission_check/borrowck_loan_kills::walk_linked_list_n_steps` has an unqualified
   `#[should_panic]` documenting a parser bug. Passing by panic does not verify
   cancellation or borrow safety. Attach it as a known tooling gap, with the
   desired scenario linked to cancellation.
5. `place_ops::drop_borrowed_is_noop` and `mdbook::interp_drop_borrowed_noop` permit
   reading `r` after `r.drop`. That conflicts with S3's agreed destruction of our
   stored reference slot. Distinguish it from `r.field.drop` through a borrowed
   receiver, which S3 intends to remain nondestructive.
6. Array leak tests are intentional witnesses of the unsafe contract: array
   destruction does not itself destroy elements. Do not classify every residual
   allocation as a bug or assert a universal no-leak anchor. Vec cleanup tests
   exercise the higher-level obligation to clean elements explicitly.
7. The Vec helper runs interpreter-only examples. These demonstrate runtime
   composition, not checker acceptance of the Vec API.
8. Several modules mix unrelated cases: boolean literals/comparisons/subtraction
   currently live in `drop_body`; book modules contain many different semantic
   claims. Move by claim, retaining snippet identifiers used by the book.

## Worktree coordination

Keep claim text and its tests in the same PR. Use an issue for an unresolved
anchor or a gap in its implementation, referencing the stable module/claim ID.
A worktree reports which claims it changes and which it merely exercises. This
lets two implementations proceed concurrently without competing to edit one
"current WIP" document. An issue's latest discussion must not silently redefine
the commitments of an older checkout.

## Suggested first migration

Review the four concrete modules and the flagged cases above. Then migrate a
small cluster without changing expectations, preserving snippet IDs and test
helpers. Label known gaps explicitly; do not mass-update snapshots during the
move. After migration, run the workspace tests and book checks. Once the layout
is agreed, update AGENTS.md and consider an inventory check requiring each test
to have a primary anchor or explicitly documented explanatory/tooling home.

The immediate goal is meaningful ownership of assertions, not a 100% affiliation
number achieved by assigning every unexplained test to a broad bucket.

## Source inventory

This records the files inventoried, including tests outside the two main test
directories. The family table above proposes how to split mixed modules.
Empty `type_system/tests/vector.rs` and `subtyping/liskov/compatible_layout.rs`
contain no test declarations and provide no coverage.

| Current source | Test declarations |
|---|---:|
| [src/grammar/test_parse.rs](../../src/grammar/test_parse.rs) | 14 |
| [src/interpreter/tests/array.rs](../../src/interpreter/tests/array.rs) | 65 |
| [src/interpreter/tests/basics.rs](../../src/interpreter/tests/basics.rs) | 11 |
| [src/interpreter/tests/block_scoped_drops.rs](../../src/interpreter/tests/block_scoped_drops.rs) | 6 |
| [src/interpreter/tests/copy_move.rs](../../src/interpreter/tests/copy_move.rs) | 3 |
| [src/interpreter/tests/drop_body.rs](../../src/interpreter/tests/drop_body.rs) | 17 |
| [src/interpreter/tests/generics.rs](../../src/interpreter/tests/generics.rs) | 8 |
| [src/interpreter/tests/mdbook.rs](../../src/interpreter/tests/mdbook.rs) | 18 |
| [src/interpreter/tests/method_calls.rs](../../src/interpreter/tests/method_calls.rs) | 7 |
| [src/interpreter/tests/normalization.rs](../../src/interpreter/tests/normalization.rs) | 13 |
| [src/interpreter/tests/place_ops.rs](../../src/interpreter/tests/place_ops.rs) | 45 |
| [src/interpreter/tests/share.rs](../../src/interpreter/tests/share.rs) | 2 |
| [src/interpreter/tests/size_of.rs](../../src/interpreter/tests/size_of.rs) | 6 |
| [src/interpreter/tests/vector.rs](../../src/interpreter/tests/vector.rs) | 10 |
| [src/type_system/pop_normalize.rs](../../src/type_system/pop_normalize.rs) | 2 |
| [src/type_system/tests/array_ops.rs](../../src/type_system/tests/array_ops.rs) | 39 |
| [src/type_system/tests/assignment.rs](../../src/type_system/tests/assignment.rs) | 4 |
| [src/type_system/tests/cancellation.rs](../../src/type_system/tests/cancellation.rs) | 10 |
| [src/type_system/tests/class_defn_wf/shared_vs_share.rs](../../src/type_system/tests/class_defn_wf/shared_vs_share.rs) | 2 |
| [src/type_system/tests/class_defn_wf.rs](../../src/type_system/tests/class_defn_wf.rs) | 14 |
| [src/type_system/tests/drop_body.rs](../../src/type_system/tests/drop_body.rs) | 8 |
| [src/type_system/tests/fn_calls.rs](../../src/type_system/tests/fn_calls.rs) | 10 |
| [src/type_system/tests/given_classes/lock_given.rs](../../src/type_system/tests/given_classes/lock_given.rs) | 2 |
| [src/type_system/tests/given_classes.rs](../../src/type_system/tests/given_classes.rs) | 7 |
| [src/type_system/tests/mdbook.rs](../../src/type_system/tests/mdbook.rs) | 58 |
| [src/type_system/tests/move_check.rs](../../src/type_system/tests/move_check.rs) | 5 |
| [src/type_system/tests/move_tracking.rs](../../src/type_system/tests/move_tracking.rs) | 5 |
| [src/type_system/tests/new_with_self_references.rs](../../src/type_system/tests/new_with_self_references.rs) | 8 |
| [src/type_system/tests/normalization.rs](../../src/type_system/tests/normalization.rs) | 20 |
| [src/type_system/tests/or_perm.rs](../../src/type_system/tests/or_perm.rs) | 34 |
| [src/type_system/tests/permission_check/borrowck_loan_kills.rs](../../src/type_system/tests/permission_check/borrowck_loan_kills.rs) | 4 |
| [src/type_system/tests/permission_check.rs](../../src/type_system/tests/permission_check.rs) | 23 |
| [src/type_system/tests/predicate_quantifiers.rs](../../src/type_system/tests/predicate_quantifiers.rs) | 9 |
| [src/type_system/tests/shared_classes_permissions.rs](../../src/type_system/tests/shared_classes_permissions.rs) | 6 |
| [src/type_system/tests/shared_classes_subtyping.rs](../../src/type_system/tests/shared_classes_subtyping.rs) | 5 |
| [src/type_system/tests/subpermission.rs](../../src/type_system/tests/subpermission.rs) | 6 |
| [src/type_system/tests/subtyping/copy_types.rs](../../src/type_system/tests/subtyping/copy_types.rs) | 12 |
| [src/type_system/tests/subtyping/liskov/cancellation.rs](../../src/type_system/tests/subtyping/liskov/cancellation.rs) | 17 |
| [src/type_system/tests/subtyping/liskov/subpermission.rs](../../src/type_system/tests/subtyping/liskov/subpermission.rs) | 18 |
| [src/type_system/tests/subtyping/liskov.rs](../../src/type_system/tests/subtyping/liskov.rs) | 13 |
| [src/type_system/tests/subtyping.rs](../../src/type_system/tests/subtyping.rs) | 46 |
| [src/type_system/tests/type_check.rs](../../src/type_system/tests/type_check.rs) | 9 |
| [src/type_system/tests/variance_subtyping.rs](../../src/type_system/tests/variance_subtyping.rs) | 3 |
| [src/type_system/tests.rs](../../src/type_system/tests.rs) | 3 |
| [mdbook-judgment/src/main.rs](../../mdbook-judgment/src/main.rs) | 7 |
| **Total** | **634** |

## First property extraction: September 25, 2026

The agreed terminology is **property** for semantic claims; **anchor** continues
to mean a source-snippet marker. Property module headers are authoritative
Markdown included in the book with `{{property module_name}}`.

- [x] Add test-only `src/properties` and extract `moves_preserve_dependencies`.
  All five test bodies and expectations are preserved; their module paths change.
- [x] Document intent, a candidate place-prefix substitution lemma, assumptions,
  and evidence in the module header. Runtime mutable-reference relocation is
  explicitly outside the established evidence.
- [x] Extend the existing preprocessor with file/directory and nested module
  resolution, leading `//!` Markdown extraction, source links, code-fence handling,
  and errors for missing, ambiguous, or undocumented references.
- [x] Include the property in Giving and document conventions in AGENTS.md.
- [x] Complete workspace tests and book validation: `cargo test --all --workspace`
  passes (624 model tests and 11 preprocessor tests). A focused preprocessor rerun
  after simplifying source-link construction also passes all 11 tests.
  `cargo build --lib`, `mdbook test -L target/debug/deps`, `mdbook build`,
  `cargo fmt --all -- --check`, and `git diff --check` pass. Generated Giving HTML
  contains the property headings, candidate lemma, scope text and source link,
  with no unresolved property directive. The migrated test content below the new
  header is byte-for-byte identical to the original module.
  Book validation still reports the unrelated missing `ref|mut place` rule
  reference and Mermaid/mdBook version mismatch; neither blocks the build.

Deviation from the early survey: start with moves, as selected in discussion,
rather than predicate quantification. No second property, automated suite-wide
affiliation check, runtime fix, issue creation, or WIP chapter migration is included.
Future work and known violations should be tracked in GitHub issues; this file
records the already existing local plan and its implementation.

### Rebase validation: September 26, 2026

Rebased the uncommitted property extraction onto `origin/main` at `3a0f202`,
preserving the upstream predicate vocabulary migration and soundness assessment.
Merged the local extraction record with the now-tracked survey and resolved the
WIP index conflict. `cargo test --all --workspace` passes (627 model tests and
11 preprocessor tests); `mdbook build`, formatting, and diff checks pass. The
existing missing-rule and Mermaid version warnings remain.

## Second property extraction: September 26, 2026

The selected property is deliberately narrower than the original predicate-wide
proposal: `given_from_duplication_requires_shared_origins`. It concerns duplication
for ordinary non-shared classes, not mutation or every predicate/permission.

- [x] Move five duplication tests from `predicate_quantifiers` into the property
  module without changing their bodies or expected results. Rename tests using
  current vocabulary and remove stale copy-predicate comments; the old
  `not_copy_single_place` test actually has two origins and is now named for its
  unique initializer.
- [x] Complete the two-origin given/shared matrix with a both-unique rejection.
- [x] Add authoritative module Markdown with the definition of an origin, examples,
  a candidate lemma, and the class/evidence limitations. Include it in the book's
  Shared permissions chapter using the existing property directive.
- [x] Update AGENTS.md; leave mutation and vocabulary tests in their existing home.
- [x] Validation: `cargo test --all --workspace` passes (628 model tests and
  11 preprocessor tests), including all six tests in the new property module.
  `mdbook build`, `mdbook test -L target/debug/deps`, formatting, and diff checks
  pass. Inspected the rendered property heading, example table, candidate lemma,
  and source link; no unresolved directive remains. The existing missing-rule
  and Mermaid version warnings remain unrelated to this extraction.

No language semantics, predicate implementation, or existing snapshots change.

### Projected origins: September 27, 2026

- [x] Add four grouped test matrices for `d1.field` / `d2.field` and
  `d1.inner.field` / `d2.inner.field`, distinguishing declared field permissions
  from permissions inherited through the container. Each covers both-shared,
  both-unique, and both mixed orders.
- [x] Check a single give succeeds in every row before checking duplication;
  negative cases assert the expected live-source give failure, not merely any error.
- [x] Extend the authoritative property prose to explain full-place types.
- [x] All 10 property tests pass, including the four new matrices (16 origin
  combinations, each checked with one and two gives). Workspace validation passes:
  632 model tests and 11 preprocessor tests. Book build/example checks, formatting,
  and diff checks pass; inspected the rendered projected-origin explanation.
  The existing missing-rule and Mermaid version warnings remain.
