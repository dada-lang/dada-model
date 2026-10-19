# dada-model

The original Rust model and mdBook are preserved in `v1/` as a working reference.
Read `v1/AGENTS.md` before changing that model. Its paths and commands are relative
to `v1/`. The v2 design draft is an mdBook in `v2/md/`, configured by `v2/book.toml`.
The book separates repository methods and specification-system requirements
(`v2/md/repo/`), Dada language goals (`v2/md/dada/`), and the heap model.
`v2/mdbook-dada` is a Rust mdBook preprocessor in the v2 Cargo workspace.
It indexes MyST-style `{anchor}`, `{definition}`, `{obligation}`, and
`{anchor-ref}` roles and renders `{heap}` fenced directives as SVG from declarative facts, with a Rendered/Facts selector.
Fenced `{grammar} File:Type ...`, `{judgment} File:Name`, and
`{rule} File:Judgment.constructor` directives pair authored LaTeX bodies with
cited Lean declarations or cases through a Rendered/Lean selector. Fenced
`{definition} File:Name ...`, `{theorem} File:Name`, and `{lemma} File:Name`
instead contain Markdown statements and explicitly delimited mathematics;
proof blocks may include high-level proof outlines. A definition takes one or
more citations to named `def`, `abbrev`, `structure`, or `inductive` declarations
and shows their complete bodies. It rejects theorem, axiom, example, and
constructor-only citations. Definition extraction supports the documented
line-oriented equation, `:=`, and `where` bodies, including qualified names.
Semantic Definition labels should have this citation-backed selector; modeling
conventions and commentary remain ordinary prose or neutral anchors. Theorem and lemma blocks
select exactly one named Lean `theorem`, including its complete proof, and reject
definitions, axioms, and anonymous examples. Definitions introduce concepts;
theorems and lemmas state proved results; proof obligations state unfinished
claims. The inline `{definition}` role remains a compatibility spelling for a
label, not a Lean citation; use a fenced definition for semantic definitions.
Inline `{obligation}` markers register stable IDs. Generic `{anchor}` markers
are neutral outside definition/proof blocks and inherit the surrounding
Definition, Theorem, or Lemma label within them. No label establishes prose/proof correspondence.
Leading identifying anchors in Markdown blocks move into the header as shields,
replacing the plain kind label without duplicating IDs. Later anchors stay with
their prose. A leading example anchor uses the Example label; later example
anchors remain neutral. All block headers place the view controls on the right, including
grammar/judgment/rule and Rendered/Facts diagram selectors; the identity stays
visible in either view. Unanchored blocks show their kind as a plain label.
Definition and theorem names may contain dots when that exact name is written in the declaration;
the extractor does not infer qualification from enclosing namespaces. Grammar blocks accept
one or more whitespace-separated citations on the opening line; judgment and rule
blocks take one. Fenced `{example} File:anchor` directives pair authored Markdown
with an anchored anonymous Lean `example` proof through the same selector.
Standalone `-- ANCHOR: name` and `-- ANCHOR_END: name` comments delimit exactly
one top-level example; they are not Lean declaration names. The selected Lean
`example` starts at column zero, continuation lines are indented, and the next
command after the closing marker starts at column zero. The authored body supports
Markdown and the book's roles and other block directives. Definitions, examples,
theorems, and lemmas cannot nest inside one another; other supported directives may occur
inside their Markdown bodies.
Use a longer enclosing fence for bodies with code fences. The `.lean` extension
is optional in citations. Missing, duplicate, malformed, or wrong-kind targets and
paths escaping `lean-source` fail the book build. The Markdown mathematics and notation explanations stand on
their own, with Lean as an associated formalization. `src/lean.rs` handles textual
source selection and HTML, not mathematical derivation or Lean elaboration. The
`lean-source` book setting locates Lean files. `v2/theme/mathjax.js` loads pinned
MathJax 4.1.3 from a CDN with CommonHTML output and New Computer Modern fonts;
mdBook's built-in MathJax 2 loader is disabled. Authored display line breaks are
preserved, with horizontal scrolling for wide equations. Explicit Markdown
math delimiters use doubled backslashes (`\\[`/`\\]`, `\\(`/`\\)`). Their
contents are protected from Markdown escapes and smart punctuation, including
TeX row breaks and primes; literal code samples are excluded.
Always group overbar expressions, as in `{\overline f}`. The command must be
immediately preceded by an opening brace and immediately followed by a literal
ASCII space. The preprocessor rejects a violation of either condition with
a source path and line number. This source lint also applies to literal TeX
samples; a test scans every Markdown file under `v2/md/`, including files absent
from the book's table of contents. Longer TeX command names are not matches.
The former `{lean.type}`, `{lean.judgment}`, and `{lean.rule}` directives are
rejected with migration diagnostics. The old grammar DSL/parser and automatic
Lean-to-LaTeX translator have been removed; Lean notation comments have no
rendering effect. The build checks citations and supported declaration or example
forms, not Lean proofs or correspondence between prose, mathematics, and Lean.
Run `just test-lean` to compile all modules, including every cited example and theorem;
review still establishes that the test covers the prose. Every semantic example
must cite its intended Lean test. Unfinished semantic scenarios are explicitly
proposed or pending. Authoring-syntax illustrations remain ordinary prose and
literal code. Review records and scripts
providing correspondence evidence remain future work. The syntax, notation
conventions, and review obligation are documented in `v2/md/repo/spec-system.md`;
theme CSS lives in `v2/theme/dada.css`.
`{informational}` at the start of a paragraph labels nonnormative commentary.
The former `{example}` paragraph prefix is rejected; use the fenced directive.
`src/routing.rs` routes diagram edges orthogonally around boxes.
Unique leases store a runtime `Place`; access paths resolve to places.
Anchor IDs must be globally unique, and unresolved references fail the build.
Heap facts group the live variable store with `vars = variables()` and slots such
as `vars.p`; this is a diagram grouping, not a frame identity. Heap facts use
`lease(node.field)` (or an array slot) for unique edge targets;
owned, showned, and shlease references target objects.
Graph structure checks do not establish heap invariants. Initial Lean state
declarations live in `v2/lean/Heap.lean`. `v2/lean/` is a Lake project pinned by
`lean-toolchain`; its default targets compile all formalization modules. The heap chapters use a shared vocabulary
of short mathematical variables; overbars denote finite ordered sequences and
partial-map arrows denote finite maps. Primitive values are an implicit common
parameter. The book explains representation abstractions and hidden proof terms
while preserving their conditions; exact representations remain available in Lean.
The declarations compile with Lean 4.35.0. Heap state contains an object map and
one ordered store of all live variable slots, including temporaries and suspended
callers' variables. Its finite-map entries record newest-first allocation order.
`VariableId` identifies a runtime binding lifetime separately from its
source name; `Place.variable` selects its slot. There are no heap frames.
The current `Operation`/`Step` slice pushes absent variables as uninitialized,
deallocates only the newest slot (which must be uninitialized), and creates
primitive, aggregate, and array objects. Creation preserves variable order,
chooses a fresh object identity, and initializes an already
allocated, empty destination with its owned reference. Aggregate field names must
be distinct; aggregate fields and array elements begin uninitialized. Empty
aggregates and zero-length arrays are allowed. Checked lemmas characterize these
local effects; they do not prove ownership exclusivity in arbitrary malformed
states. `Operation` now uses the common `Primitive` parameter for primitive
creation. The future execution semantics will α-rename bindings to fresh identities
and manage scope and cleanup. Heap allocation checks absence only from the live
map, so freshness across completed variable lifetimes remains an execution-layer
obligation. Object creation similarly checks current object-map absence;
identity reuse and reference invalidation remain to be specified.
`Invariants.lean` defines occurrence-sensitive ownership over every variable,
field, and array slot, including liveness of owning targets. Initial-state,
allocation/creation-step, and reachable-state preservation are proved.
`Places.lean` implements slot lookup/update and proves locality and key/order
preservation. `PlaceEffects.lean` proves ownership preservation for concrete
reference updates. `Destruction.lean` handles final-owner release of objects
without initialized contents. `PlaceOperations.lean` defines `PlaceEffect` for
unique give, unique lease/sublease, owned/showned share, borrowed/nonfinal-showned
release, and finite recursive final-owner destruction, with preservation for every
case. Recursive destruction requires the parent occurrence to be the last owner;
child order is unspecified. `PlaceExamples.lean` checks exact successor states.
`ReferenceUpdates.lean` maps references throughout variables, fields, and arrays;
`Moves.lean` defines consuming transfer followed by simultaneous dependent-lease
retargeting. `MoveValidity.lean` proves preservation of successful finite reference
resolution to the same object and effective permission; it does not prove activity.
`Access.lean` resolves paths and computes their effective permissions.
`PathOperations.lean` defines `PathStep` and combines it with `Heap.Step` in
`MachineStep`; ownership is proved for every step and `MachineReachable` state.
`Invariants:AllocatedObject` means membership in the object map.
`WellFormed.lean` separately defines `OwningReachable` by finite paths from all
variable roots through owned or showned references, and `ReferenceReachable`
by structural paths through any successfully resolved reference. This structural
relation does not accumulate operational access restrictions. `WellFormed` has
three direct clauses: every allocated object has an owning path from a variable;
every existing slot is uninitialized or contains a reference resolving to an
owning-reachable (live) object; and a unique owner is the sole owning occurrence
of its target. `WellFormed.equivalent_conditions` proves exact equivalence with
`OwnershipInvariant ∧ RootedOwnership ∧ NoDangling`. Those predicates remain
proof helpers, derived from the direct definition; they are not extra conditions
in the state chapter. Ownership accounting is defined in `properties.md` for the
weaker preservation results. The formalization proves agreement of
allocated/live/reference-reachable objects, initial well-formedness, preservation
by consuming moves into variables, and ownership consequences without an
execution-reachability premise. Arbitrary field/element destinations do not have
that move preservation theorem; storing an owner inside its target can lose
rooted liveness. `state.md` introduces state
components and lookup, then well-formedness by definition and its consequences.
Its slot-lookup definition pairs the partial mathematical `S(p)` with both
`Places:readSlot` and `Invariants:Stored`; missing lookup is distinct from a
present uninitialized slot. Allocated and live objects, initial state, owning occurrences,
and other semantic definitions expose their associated Lean bodies.
A separate cited reachability definition relates states to execution histories.
Stack lemmas, α-renaming, and non-revival obligations belong in operations.
Full well-formedness preservation is not established: a checked reachable sequence
allocates two variables, creates an owner, shares it, then drops that owner,
leaving a dangling shared lease. Ownership still holds. Do not claim that
no-dangling in one state supplies lifetime freshness or prevents identity revival.
`PathExamples.lean` checks exact successor states. Give consumes unique ownership,
reborrows through leased access, and copies shared references. Showned duplication
requires an actual stored showned edge, rather than inherited shared access to an
owned edge. Destructive showned drop also requires a unique prefix route; copied
shared views need a separate representation account. Borrowed path-drop leaves
the state unchanged; `PlaceEffect` slot release is a separate cleanup
effect. Whether explicit drop should release borrowed handles remains open.
`AccessConflicts.lean` defines a static live-lien table over syntactic
paths, with caller-supplied live liens. It is separate from runtime `PathStep` and
does not supply liveness, alias/type analysis, or dynamic invalidation. Do not
claim that ownership preservation establishes borrow validity. The book states
the current semantics directly; implementation investigations and comparisons
with earlier versions are not part of the semantic exposition. Historical
context belongs only in the older-versions appendix. The separate chapter is
`v2/md/place-operations.md`; `properties.md` distinguishes proved ownership from
pending safety/termination obligations. Claim-content extraction and
review/evidence verification remain unimplemented. Read `v2/md/questions.md` before formalizing unresolved semantics.
Keep candidate claims distinct from established proofs and executable examples.

## Build and test

- `just test` runs the v1 Cargo and mdBook example tests, v2 preprocessor tests,
  and the Lean project.
- `just test-lean` runs `cd v2/lean && lake build --wfail` with pinned Lean 4.35.0.
- From `v1/`, run `cargo test --all --workspace` and `mdbook build`.
- From `v2/`, run `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`,
  and `cargo test --workspace` for changes to the Rust tooling.
- `just book-v2` builds the v2 draft; `cd v2 && mdbook serve` previews it.
- `just book-tools` installs pinned mdBook 0.5.4 and mdbook-mermaid 0.17.1;
  the custom preprocessors are built from the two Cargo workspaces.
- `just site` builds both books and the root redirect into the ignored `_site/`
  directory, using the same script as CI. Stable Rust is required.

## Publishing

GitHub Actions workflows remain in `.github/workflows/`. The Pages workflow
tests v1 book examples, checks the pinned Lean project, and builds both books on pull requests and pushes to
`main`; only `main` deploys. It installs tools using `pages/install-tools.sh`
and assembles the site with `pages/build.sh`: `pages/index.html` at the root,
the older book under `/dada-model/v1/`, and the new book under `/dada-model/v2/`.
The root redirects to v2. Its older versions appendix
(`v2/md/appendices/older-versions.md`) explains the a-mir-formality-based v1
model and links back to its book using the assembled site's relative paths.
Each book's `site-url` matches its published prefix for 404 asset resolution.
Keep generated v1 source links pointed at the repository's `v1/` directory.
The checked-in v1 Mermaid initializer must match mdBook's theme menu IDs.
See `pages/README.md` for preview commands, dependencies, and the required
GitHub Actions source setting in repository Pages settings.

Keep this file and `v1/AGENTS.md` current when changing the repository layout.
