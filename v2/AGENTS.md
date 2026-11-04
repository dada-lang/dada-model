# Working on the v2 specification

Read the repository-root `AGENTS.md` for the model's current status and source
selection constraints. This file describes the structured authoring and evidence
loop. Build later layers from Given and Shared. The earlier monolithic heap
draft and its Lean modules have been removed; do not restore them as an implicit design
reference. Do not claim that partial evidence coverage covers the whole book.

## Units and scope

- Every new-style specification unit under the configured book source root (`md/` here) requires evidence.
  `{future-note} ID` is for exploratory, nonnormative notes: it rejects `:lean:`,
  `:rust:`, `:tests:`, and `:status: draft`. Notes allow `:uses:` and links for
  context, remain indexed and checked for structure and dependencies, and cannot
  receive correspondence reviews. Their lack of formalization does not block publication. `spec.json` additionally
  selects strict chapters and policy inputs. Inspect it before changing coverage. New semantic content in strict chapters belongs in
  named units, including its explanatory prose and mathematics.
- The opening argument is the ID: ```` ```{definition} unique.syntax.place ````.
  Put source targets in `:lean:` and contextual unit IDs in `:uses:`, then a
  blank line and the authored body. Do not put the Lean target on the opening
  line in new structured content.
- Use definitions for concepts and judgments, and theorem/lemma units for results.
  Definitions do not require proofs.
  Examples cite a Lean case that states their intended setup and result.
  For Markdown-first review, `:status: draft` preserves the intended kind with
  a separate Draft indicator. Drafts may omit source citations; supplied
  citations remain checked by kind. Drafts fail evidence validation and cannot
  receive affirmative correspondence records. Complete the formalization and
  remove draft status before recording approval. Use `p→` and `p→share` in the
  source language presentation.
- Meta requirements use `:rust:` implementation targets and `:tests:` test
  targets. Do not silently treat implementation inspection as test execution.
- Structured units reject mdBook include/playground/rustdoc-include expansion,
  even in literal samples, and nested legacy citation directives. Write a body's
  text directly; use separate units and `:uses:` for related source selections.
  The renderer checks original chapter source before processing expanded input.
- `book.toml` defines source roots for both rendering and inventory and is a
  required freshness input. Roots remain inside the project; do not independently
  hardcode `lean/` in another consumer.
- The authoring guide is `md/repo/authoring.md`; the evidence contract is
  `md/repo/spec-system.md`. Detailed review instructions are in
  `md/repo/correspondence-review.md`. The Unique/Shared module protocol
  is in `md/repo/layer-extension.md`.
  Follow `md/repo/writing-style.md` for intent-first explanations, motivating
  examples, notation, and narrative order.

## Edit, check, and review

1. Make the source and book edits needed to express the intended behavior.
   Include context through `:uses:` and citations so that a comparison can be
   reproduced from its bundle. Keep unrelated work intact.
2. Run `cargo run -p mdbook-dada --bin dada-spec -- status --explain` from this
   directory. Fix malformed units and unresolved targets first.
3. Run `cargo run -p mdbook-dada --bin dada-spec -- prepare UNIT_ID`. Read the
   emitted bundle and review its required unit, selection, policy, and extra
   context inputs. Inspect additional source context as needed and list only
   inputs actually examined. A fresh reviewer is preferred;
   preparation itself is not approval.
4. Write a review with its bundle digest, reviewer identity/provenance, examined
   input keys, `corresponds`/`mismatch`/`inconclusive` conclusion, specific
   comparison rationale, and limitations. Follow the current review format and
   procedure. Do not invent a review or alter old hashes to clear a failure.
5. Record it with `cargo run -p mdbook-dada --bin dada-spec -- record BUNDLE_PATH
   REVIEW_JSON_PATH`. If inputs changed, prepare and review again. Explicitly list earlier active
   decisions for the same unit in `supersedes`; every unsuperseded decision must
   be current and positive. A stale replacement cannot restore an earlier
   approval. Inputs consulted outside the bundle must first be made explicit
   dependencies.
6. Run `cargo run -p mdbook-dada --bin dada-spec -- check` and the relevant
   mechanical checks. Report correspondence and mechanical results separately.

Review theorem statements, including assumptions, quantifiers, and hidden
parameters, for correspondence with intent. Leave proof correctness to Lean;
do not require prose proof outlines or recheck tactic internals. For examples,
check that the actual proposition covers the described scenario. For tooling
requirements, inspect behavior and test coverage and state limits explicitly.

## Verification

From `v2/`, run `cargo fmt --all`,
`cargo clippy --workspace --all-targets -- -D warnings`, and
`cargo test --workspace` after Rust changes. The ordinary Cargo evidence test
performs deterministic syntactic validation of required inputs and current
records. It does not launch agents, access the network, or compile Lean.

From the repository root, run `just test-lean` when changing the formalization
and `just book-v2` for authoring or rendering changes. `just test-lean` uses
`lake build --wfail`, which rejects warnings, including those emitted by Lean `sorry`.
Do not introduce admissions, suppress `warn.sorry`, or disable this check. Any future allowance must
require an explicit opt-in. The evidence check does
not replace these commands or assert that they have been run. Preserve failure
evidence and fix the underlying cause rather than weakening configured coverage.

Content-hashed bundles and review records live in `evidence/`. Commit required
records with their reviewed inputs when a commit is requested. Full selected
source context is currently fingerprinted conservatively, so proof-only or
otherwise irrelevant edits in a dependency can require renewed review. Do not
claim that the textual selector computes Lean's semantic dependency graph.

## Incremental language layers

Shared distinguishes nominal declaration kinds: `class` is not shareable,
`struct` is shareable, and `shared struct` constructs shared references
immediately. `Kind.isStruct` and `Typing.StructType` formalize `struct(T)` for
both struct forms. `Typing.ClassTable.WellFormed` requires their field types to
be structs; `KindValid` permits only given class types and shared shared-struct
types. Operational `StructReference` and `StructArguments` guards prevent
untyped sharing or construction from bypassing the restriction.
`Shared/KindSafety` proves preservation of the reference-kind and struct-field
invariants, with `WellFormedState` combining them with structural well-formedness.
`Shared/KindChecks` checks declaration rejection, immediately shared construction,
copying through its fields, and class-sharing rejection. Given declarations embed
as classes in both the operational and typing correspondence.
`md/functions.md` now has Lean-backed syntax, call/return and typing rules,
examples, and Shared-fragment correspondence. `lean/Functions/` explicitly
imports Shared's call-free storage, evaluation, and typing foundation; its call
syntax, machine, and judgments are separate. `Correspondence/SharedFunctions`
proves forward/backward steps (arbitrary successors), traces, typing, completion,
and stuckness. Program execution correspondence in `SharedFunctionsFrames` matches all
steps and boundaries exactly, including the shared initial-frame exit. The
older `SharedFunctions` results describe auxiliary local-frame observations. The machine has an explicit
frame stack and collects unreachable objects after every transition, including
return and initial-frame exit. The collector is a noncomputable mathematical
reachability filter, not an executable traversal. Completed frames retain no
stores; a terminal step leaves an empty heap and preserves the allocation counter.
`Functions/StackTyping` defines compatible frame/continuation typings and
realization of all frame roots in the common heap. `Functions/Safety` proves
progress, preservation for every successor, compatible ownership, empty typed
completion, and safety of every finite execution prefix of a well-typed program.
Recursion remains permitted without a termination claim. The proof uses
`Shared/TypingBindingPending` for arbitrary additional roots and
`Shared/TypingCollection` for collection after discarding roots.
`Functions/SafetyChecks` applies the theorem to nested and recursive calls.
`md/destructors.md` and `lean/Destructors/` add explicit destruction. Class drops
elaborate to calls in a dedicated destructor-name namespace with one given whole
receiver and no result. Struct drops give and discard without running code.
Every body must leave only empty or struct locals after evaluating its result;
raw return and initial exit also check the runtime store. Destructor signatures
are visible recursively, but empty class destructors fail consumption checking.
`Destructors/Safety` proves progress, preservation, finite-prefix safety, empty
completion, and that collection after every typed raw step retains all class
objects. `Destructors/Collection` proves that discarded struct roots cannot hide
class garbage, using nominal correctness of fields even when omitted by views.
`Destructors/Checks` and `ExecutionChecks` cover consumption, rejected partial
and absent destructors, struct effects, complete nested destruction, and recursive
execution. `Correspondence/FunctionsDestructors` preserves and reflects steps of
the embedded Functions fragment under an explicit exit condition and reflects
arbitrary successors and traces. Both chapters have inherited machinery appendices.
Destructors are
followed by Assignment, Branching,
Looping explicit with declared invariants, and Looping natural with inference.
Reuse preceding-layer machinery when straightforward, with explicit imports
and correspondence theorems stating the preserved fragment and changed boundaries.

`lean/Unique/` defines the Given language; `lean/Shared/` independently defines
the Shared language. Given uses classes; Shared adds structs and shared structs. Both support empty
declarations, ordered named fields, fresh-variable `let` statements, recursive constructor expressions,
and tagged, monotonically allocated object IDs. `Eval` and `EvalArgs` evaluate
arguments left to right within one statement step; temporary roots remain
accounted for by `WellFormedWith` until construction or binding consumes them.
Assignment, drop, primitives, scopes,
and borrowing are outside these layers.

`Shared.Give` moves through unique paths and copies through shared paths. Modes
belong to references, not objects. Copying a unique final reference through
shared access changes that stored reference to shared before copying it. Sharing
a container leaves its field references unchanged. `Shared/Liveness` proves that
a well-formed state cannot have both an entirely unique path and a shared path
to the same object.
`Unique/Soundness` and `Shared/Soundness` prove preservation of structural
well-formedness; the respective `Liveness` modules derive rooted liveness.
`Common/Rooted` supplies bounded-rank graph reasoning.
`Common/FiniteMap` and `Common/FiniteMapExamples` supply the evidence pilot's
small utility example. Renderer fixtures live separately under
`mdbook-dada/tests/fixtures/lean/` and do not specify language behavior.
`Correspondence/UniqueShared` embeds full programs and configurations and proves
forward/backward steps, finite traces, initial states, completion, and stuckness.
The backward theorem quantifies over arbitrary Shared successors.

The intervening chapter `md/given-typing.md` has Lean definitions for signed
views, typing judgments, and storage realization in `Unique/Views`,
`Unique/Typing`, `Unique/TypingRealization`, and `Unique/TypedConfigurations`.
`Unique/ViewChecks`, `Unique/TypingChecks`, and `Unique/TypingExecutionChecks`
check the linked examples, including their complete runtime executions.
`Unique/TypingSafety` proves expression soundness, progress, preservation,
and completion after exactly one local step per statement, with frame-level completion
after one additional exit step. Expression soundness
includes evaluation existence and preservation for every evaluation, with
arbitrary pending values. `Unique/TypingGiveSoundness` and
`Unique/TypingBindingSoundness` connect the static rules to the operational
semantics; no operational-success premises are added to typing.
`Unique/ViewNormalization` proves preservation of positive and negative
observations. `Unique/ViewCanonical` proves well-formedness preservation
and independence from entry order.
The separate `Unique/Unpacking` extension has operational rules, structural
well-formedness preservation, and a faithful embedding/reflection of the base
Given machine. `Unique/UnpackingChecks` checks field-order permutations, empty
slots, and the complete book example. `Shared/Unpacking` extends Shared with
the same binding patterns and requires a unique reference for unpacking.
`Correspondence/UniqueSharedUnpacking` proves forward and backward execution
correspondence for the extended machines, including arbitrary successors,
completion, and stuckness.
`Correspondence/UniqueSharedTyping` preserves and reflects typing on the
all-given fragment, including unpacking patterns.
Positive view entries expose whole declared subtrees; negative entries mark
existing empty slots; unlisted branches are unknown and inaccessible.
View entries must have distinct, prefix-incomparable paths. Expanded views are
valid input and normalize by collapsing complete positive subtrees. The formal
type is always `C.A`; bare `C` abbreviates `C.{ε}`. Emptying uses `T[-ρ]`.
Normalization must not invent initialized empty-class fields; only the known
root of an empty class permits the empty-view special case.
Whole constructor arguments remain a first-pass restriction.
Unpacking requires known status for every direct field and transfers empty
slots to empty bindings; interiors of transferred objects may remain partial.
`md/dada/future-extensions.md` records generic views as a future proposal,
including the unresolved representation of an initialized field with no exposed
interior. Do not implement that proposal as part of the current type system.

`md/shared-typing.md` adds only `given` and `shared` permissions.
`Shared/TypingViews` composes permissions and reuses Given signed views through
a nominal class-table projection. `Shared/Typing` defines the static give
operation and expression, binding, and statement typing. `Shared/TypingRealization`
relates each reference to its view, including effective modes on hidden paths.
`Shared/TypingPaths` and `Shared/TypingPathEffects` account for pending roots as
well as stored roots: a unique route excludes other routes, while promotion
through shared access preserves existing aliases.
`Shared/TypingSafety` proves expression soundness for arbitrary pending values,
progress, preservation, and completion in exactly one local step per statement; `Shared/FrameSafety`
extends this to program completion after one additional exit step.
`Shared/TypingChecks` and `Shared/UnpackingChecks` cover the chapter examples.
Path-dependent permissions and permission/type unions remain future extensions
in `md/dada/future-extensions.md`.

The strict chapters are `md/given.md`, `md/given-typing.md`, `md/shared.md`,
`md/shared-typing.md`, `md/functions.md`, and `md/destructors.md`, plus future extensions
and the evidence pilot. Deferred destructor conveniences remain nonnormative future notes.
The future notes are publishable without formalization; adding a formalization
citation to a future note is an error. Changes to the evidence configuration and these instructions also
invalidate earlier reviews; do not claim those records remain current or
refresh their hashes without performing new reviews.
Keep their semantic content in cited units and renew affected review records
after changes. `lake build --wfail` includes both layers and correspondence.

## Mechanical execution receipts

`spec-checks.json` configures `dada-spec run-check NAME`; `mechanical-status`
reports current receipts independently of correspondence decisions. The runner
captures command/version output, status, declared source contents and directory
membership before and after execution, including its configuration and source.
It retains failed runs. `.git`, `.lake`, `target`, `book`, and `evidence` trees
are excluded. These snapshots are not a hermetic environment or authenticated
execution. Syntactic checking validates saved receipt integrity without running
commands or requiring a pass (the Cargo evidence test cannot require a receipt
for its own execution). The Lean assumptions profile rebuilds before printing
the explicit theorem list in `lean/CheckAxioms.lean`. Add theorem queries there
when expanding the set of proof assumptions to report.

Renderer contracts live in `md/repo/renderer-contracts.md`; source/test citations
and checked-in theme JS/CSS are conservative correspondence inputs. A source
change requires renewed review, not a manufactured positive receipt or verdict.

Given and Shared expose their public program machines in `Unique/Frames` and
`Shared/Frames`: one optional initial frame, eager reachability collection after
every local statement, and an explicit frame-pop step. `Step`/`Unpacking.Step`
in the older modules are auxiliary local-frame relations, not complete program
lifetimes. `FrameSafety` proves progress, preservation and exactly n+1 total
steps, retaining a pre-exit realization witness after n statement steps.
`FrameChecks` covers empty-program exit and allocation followed by reclamation.
`Correspondence/UniqueSharedFrames` relates framed steps and boundaries;
`Correspondence/SharedFunctionsFrames` gives exact correspondence with Functions.
Functions reuses the Shared storage collector with the roots of all live frames.

## Links and conceptual order

Use the existing Markdown, anchor-reference roles, and MathJax `\href` links;
do not add a parallel concept-tagging syntax. `dada-spec links [--json]` derives
link occurrences and reading order from `SUMMARY.md` and source positions.
Internal destinations are checked against both chapter path and anchor. Use
`.html` paths in authored MathJax links, because MathJax does not run mdBook's
Markdown URL rewriting.

`links.coverage/UNIT`, `links.target/HASH`, and `links.forward/HASH` are generated
review subjects for the existing `prepare` and `record` commands. Read
`md/repo/link-audits.md` and the link-review policy in
`md/repo/correspondence-review.md`. Examine unlinked prose and math as well as the
extracted occurrence list. Target evidence must identify a clear landing, not
justify a buried definition by selecting its precise span. Prefer rearranging
forward references; retained ones require explicit source signposting and
reasons for necessity and minimal use. Navigation classifications are reviewed,
not blanket exceptions. Local references must follow the actual definition.

Draft units and future notes also need link audits. Editorial audits of future
notes do not assert correspondence with a formalization. Saved
audits retain exact source/target snapshots, relevant chapters, order/position
metadata, policy, and tool/theme inputs. Their deterministic validation runs in
the existing Cargo evidence test without invoking an agent, network, or Lean.
