# Specification system design

The specification consists of named units of Markdown and mathematics, each
linked to its formalization or implementation. The Rust library in
`v2/mdbook-dada` supplies both the mdBook renderer and the `dada-spec` evidence
commands. A unit has one stable identity, a complete authored body, and explicit
source and context dependencies. The renderer and evidence checker use the same
unit boundaries.

Every structured unit under `md/` participates in the evidence inventory.
`v2/spec.json` additionally lists strict chapters, where semantic prose must be
inside units using the syntax described in [Authoring units](authoring.md).
The renderer also retains the earlier citation syntax for compatibility.
Successful validation does not imply that every paragraph of this book has
been reviewed.

A source citation, correspondence review, passing test, and checked Lean proof
answer different questions. A shield identifies a unit; it does not certify it.
The [review procedure](correspondence-review.md) explains how to prepare and
record evidence, and [extending the model](layer-extension.md) describes how
independently understandable semantic layers are related.

{anchor}`meta.anchors.identity`
Each named claim has a unique identity and one defining source location. References
and generated views resolve to that definition. Missing or ambiguous identities
are reported as errors rather than silently omitted.

{anchor}`meta.anchors.content`
A structured unit's opening and closing fences delimit its complete content,
including its options, prose, mathematics, qualifications, and examples. The
opening-line argument is its stable ID. Rendering and review use that complete
unit, before Markdown escaping or HTML generation. A legacy inline anchor names
a location but does not establish an evidence boundary.

In strict chapters, semantic explanations belong inside units. New terminology
links to the unit that introduces it; explanatory examples cite Lean cases that
state the behavior described. Headings organize the reading order without adding
untracked semantic claims.

{anchor}`meta.correspondence.coverage`
A claim can be associated with multiple definitions, operations, examples, tests,
and propositions. The associations identify their exact targets. The system
records explicit gaps and the scope covered by each association; the existence
of a link alone does not establish adequate coverage.

{anchor}`meta.reviews.correspondence`
Human or agent review assesses whether the associated views collectively express
a coherent, intended design. It examines quantifiers, assumptions, exceptions,
and relevant definitions, and considers cases that satisfy the propositions but
violate the prose. Reviews retain claim-specific reasoning and unresolved issues.

Neither English, propositions, nor code automatically prevails in a discrepancy.
The discrepancy must be discussed; resolving it can change any of those views or
the intended design. Proof difficulty alone does not establish that a design is
flawed or a proposition false.

{anchor}`meta.reviews.freshness`
A saved correspondence review applies only to its recorded claim, propositions,
assumptions, and relevant definitions and evidence, under its recorded review
policy. Changes affecting those inputs require renewed review. A stored line number is
only a diagnostic location and does not participate in the bundle digest.
Moving text within a conservatively fingerprinted source file still changes that
file's contents and therefore invalidates the current implementation's evidence.

Changing the definition of `live`, for example, can invalidate review even when a
theorem's displayed statement is unchanged. A change confined to proof technique need not change the mathematical intent.
The current implementation conservatively fingerprints all local Lean sources
for units with Lean citations, so it also invalidates reviews after proof-only
edits or changes elsewhere in the local formalization. This can require extra review; it must not silently omit a dependency.
Finer tracking of elaborated statement dependencies is a future refinement.

{anchor}`meta.reviews.recording`
Preparing review inputs does not approve them. Recording a decision checks that
its inputs still match the current sources and retains the reviewer identity and
reasoning. Automated checking reports stale or missing decisions; it does not
manufacture approvals to make a check pass.

{anchor}`meta.evidence.status`
The system distinguishes claims awaiting formalization, proposed formalizations
awaiting review, reviewed formalizations with incomplete proofs or coverage gaps,
and mechanically checked proofs under recorded assumptions. It separately
identifies executed examples and tests. Partial coverage of a claim is not
presented as establishment of the whole claim.

Build success, a source association, a review judgment, a passing test, and a
checked proof remain distinct evidence. Unfinished formalization stays marked
draft and prevents the evidence check from passing.

Structured units separate kind from readiness: `:status: draft` keeps the
Definition, Example, Theorem, or other kind label and adds a Draft indicator.
A draft may omit citations; supplied citations retain their kind checks.
Drafts fail evidence validation and cannot receive an affirmative correspondence
record. Definitions introduce concepts and judgments without asserting a result
to prove. Theorems and lemmas state results; draft status marks proposed results
whose formalization is unfinished.

{anchor}`meta.proofs.assumptions`
Evidence presented as a checked proof identifies its proposition, checked source
version, and assumptions, including admitted results or additional axioms.
Standard verification uses `just test-lean`, whose `lake build --wfail` rejects
warnings, including those emitted by `sorry`; do not suppress `warn.sorry`.
Any future allowance for admissions must
require an explicit opt-in; an admitted statement must not be reported as proved.

{anchor}`meta.rendering.faithfulness`
Mathematical views render the notation authored in the Markdown, and Lean views
extract their cited source. Graph renderings derive from explicit state facts;
layout hints do not silently add semantic relationships. Readers can inspect the
formalization associated with a mathematical view and the facts underlying a
diagram. Extraction preserves the cited source; correspondence between authored
mathematics and that source requires a separate review.

The Markdown supplies a self-contained mathematical account. Its definitions and
explanations can be read without opening the Lean files, whose citations identify
associated formalizations for comparison.

{anchor}`meta.system.self_specification`
The tooling's review and rendering contracts are structured units in
[Implementation contracts](evidence-pilot.md) and
[Renderer contracts](renderer-contracts.md). They cite Rust symbols and tests
and require the same recorded comparison as language units.

```{definition} meta.system.remaining_coverage
:rust: mdbook-dada/src/inventory.rs:Inventory::load mdbook-dada/src/inventory.rs:Inventory::inputs mdbook-dada/src/evidence.rs:check
:tests: mdbook-dada/tests/evidence_validation.rs:complete_current_reviews_pass_and_remain_distinct_from_mechanical_checks mdbook-dada/tests/evidence_validation.rs:prepared_bundles_are_not_completed_reviews mdbook-dada/tests/evidence_validation.rs:explicit_dependencies_and_unit_links_must_resolve mdbook-dada/tests/evidence_validation.rs:hidden_markdown_chapters_cannot_escape_required_evidence
:uses: meta.syntax.anchors.identity meta.syntax.inline_and_block meta.math.source_view meta.math.typesetting meta.math.runtime meta.math.overline.braces meta.math.definition.selection meta.math.judgment.selection meta.math.theorem.selection meta.examples.selection meta.lean.definitions.navigation meta.syntax.heap.nodes meta.syntax.heap.validation meta.syntax.heap.rendering meta.syntax.heap.routing meta.evidence.mechanical_execution

The *tooling review inventory* includes the renderer contracts linked here, with
their exact implementation and test selections. Every structured unit under the
book source root, including dot-prefixed files and directories, requires current
positive correspondence evidence, even when its chapter is not strict about surrounding prose. Explicit dependencies must name
existing units and become review inputs.

Mechanical execution records remain separate from correspondence judgments. A
review cannot stand in for a command result, and a command result cannot approve
a review. The inventory checks these declared boundaries; it does not discover
unwritten requirements or prove that tests exercise all possible behavior.
```

## Evidence and validation

{anchor}`meta.evidence.inputs`
The checker derives a required input set from the current unit inventory. It does
not accept a review's own list as the definition of what must have been reviewed.
That set includes the complete authored unit, every exact cited Lean declaration,
its required source context, referenced units, and the review policy. Meta units
also identify implementation and test targets. Their source files and declared
dependencies are review inputs. Tool and schema versions, including `book.toml`, participate in freshness.
Rendering and inventory use the same configured book and Lean source roots.
Structured units reject mdBook expansion directives and nested legacy citation
blocks; separate units and explicit dependencies keep those sources reviewable.

A bundle retains the exact input contents and content hashes in JSON, together
with source identities and locations. A reviewer can retrieve what was considered,
and another reviewer can inspect the same evidence later. A repository revision
is useful provenance but does not replace these snapshots. Changing an unrelated
file need not invalidate a review; changing an input does.

{anchor}`meta.evidence.minimum_inputs`
Syntactic validation requires the authored unit and every cited formalization to
be present under the correct input identities and to match current source.
Substituting a different declaration, dropping a citation or dependency, or
changing snapshot contents without updating their hashes is an error. Matching
hashes establish input identity, not mathematical correspondence.

{anchor}`meta.evidence.decisions`
A completed review records its bundle digest, reviewer identity, examined inputs,
conclusion, rationale, and limitations. Conclusions distinguish correspondence,
mismatch, and an inconclusive comparison. A prepared packet is not a completed
review, and a mismatch is not positive evidence. Required positive review cannot
be satisfied by merely creating a packet or filling in a conclusion field.
Decisions may explicitly supersede earlier decisions for the same unit, including
ones made against different input bundles. Every unsuperseded decision must be
current and positive; a stale replacement cannot silently restore an older
approval. The retained records preserve the decision history.
Draft units fail evidence validation and cannot receive affirmative decisions.
A cited theorem statement alone does not establish that its proof was checked.

The examined-input list must cover the authored units, exact Lean/Rust/test
selections, policy, and extra files supplied with `prepare --input`. Conservative full-source and
tool snapshots remain available for freshness and deeper inspection; a reviewer
records them as examined only when actually used. The list is a syntactic
attestation, not mechanical proof that reading occurred.

{anchor}`meta.evidence.workspace_test`
An ordinary Cargo integration test validates the configured evidence through the
same library used by `dada-spec check`. Running `cargo test --workspace` from
`v2/` therefore checks evidence presence, required inputs, schema, and freshness.
This validation is deterministic and syntactic: it invokes no agent, network
service, or Lean compiler. It cannot decide whether a recorded rationale is
persuasive or a theorem captures the intended behavior.

Diagnostics use `annotate-snippets` to identify the relevant unit or citation and
explain the repair. Missing or stale evidence directs the author to prepare a
new bundle, perform its review, and record the result. A check must not refresh
hashes or generate favorable reviews on the author's behalf.

{anchor}`meta.evidence.self_validation`
Meta requirements can cite Rust implementation symbols and named tests using
`:rust:` and `:tests:`. Their correspondence reviews use the same snapshots and
freshness rules as language units. Tests exercise specified cases and rejection
paths; they do not prove all possible behavior. The validator's own adversarial
tests remain necessary even when a review of the validator is current. Its
version is an input to evidence validation, and generated evidence is not an
input to its own hash.

The command and review formats are described in
[Correspondence review](correspondence-review.md). Mechanical Lean checking
remains a separate `just test-lean` invocation. Mechanical records retain actual
command outcomes separately; a recorded review is not an assertion that Lean or
Cargo was executed.

## Rendering and source selection

The [renderer contracts](renderer-contracts.md) specify identities, supported
blocks, mathematics, source extraction, and diagrams. Each contract cites its
implementation and tests. The [authoring guide](authoring.md) gives the syntax
for writing units. The contracts describe textual processing; correspondence
review and Lean compilation remain separate checks.

## Mathematical presentation and review

{anchor}`meta.math.source`
A grammar, judgment, or rule block contains authored mathematical notation and
citations into Lean. A definition block contains an authored Markdown explanation
with citations to its Lean formalization. A theorem or lemma block contains an
authored Markdown statement, with a citation to its Lean theorem and proof. These accounts
are part of the Markdown specification and stand on their own, with symbols and
assumptions explained in the book. The preprocessor renders the authored account
and extracts the cited source; it does not derive mathematics from Lean.

{anchor}`meta.lean.definitions.source`
Lean files contain the formal declarations cited by the book. The mathematical
account and its Lean formalization are maintained independently and compared
through explicit correspondence review. Neither version automatically prevails
in a discrepancy; resolving it can change either view or the intended design,
as in {anchor-ref}`meta.reviews.correspondence`.

{anchor}`meta.lean.definitions.presentation`
The mathematical presentation may use conventional symbols and omit Lean's
implementation details under explicit notation conventions. The Lean view
retains the original declaration, including fields, proof arguments, and derived
instances. The renderer does not infer a mathematical grammar from these details.

{anchor}`meta.math.identifiers`
The book defines a shared vocabulary of mathematical categories and metavariables
for use across chapters. Short conventional letters denote variables; upright
text denotes multi-character constructor or helper names. A notation key relates
these symbols to their meanings and cited Lean declarations. Changing notation
requires updating uses and the relevant correspondence explanations together.

{anchor}`meta.math.fields`
An authored grammar may use positional constructor arguments when the surrounding
notation key and prose make their meaning unambiguous. The book explains how
these arguments correspond to Lean's named fields. Any omission or abstraction
of a field must be stated; a shorter presentation must not silently discard a
semantic distinction.

{anchor}`meta.math.containers`
An overbar denotes a finite ordered sequence, and `K ⇀ V` denotes a finite map
from keys in `K` to values in `V`. The notation abstracts from Lean's `List`,
`Array`, and `FiniteMap` representations. The representation and its associated
proofs remain available in the cited source. See
{anchor-ref}`meta.syntax.lean.mathematical_containers`.

{anchor}`meta.math.abbreviations`
Authored notation may abbreviate terms and suppress proof terms under stated
conventions. Implicit parameters must be explained where introduced. Conditions represented
by proof arguments remain explicit: hiding the proof of freshness or distinctness
does not remove that condition. Equations introducing intermediate names must
preserve their dependencies and scopes.

{anchor}`meta.math.heap_representation`
Each language chapter explains its own representation conventions. For example,
Given writes an empty slot as \\(\bot\\) and an occupied slot as an object
identity; Lean represents these as `none` and `some object`. Such abbreviations
must preserve distinctions used by the rules. A list may be presented as a map
only under the stated uniqueness conditions, and any order relevant to the
semantics must remain visible. Omitting a proof term does not omit its condition.

{anchor}`meta.math.rule.layout`
Each premise occupies its own line above the inference bar. Intermediate values
can have short names with defining equations. Rules use the shared vocabulary
consistently in premises and conclusions, including the judgment's introduced
notation. Grammar alternatives align with their definition symbol, as described
in {anchor-ref}`meta.syntax.lean.alignment`.

{anchor}`meta.math.correspondence`
A mathematical block must express the intended content of its cited Lean source
under the book's notation conventions. Review checks represented categories,
variables, quantification, constructor fields, premises, conclusions, scopes,
and hidden parameters or proof arguments. A source citation alone is not evidence
that this correspondence holds. A discrepancy can require changes to either view
or to the intended design, as in {anchor-ref}`meta.reviews.correspondence`.

For example, a rule may give a short name to the state obtained by clearing a
slot. The Markdown defines that name and the affected location; the renderer
does not reconstruct the update from Lean.

{anchor}`meta.math.correspondence.evidence`
Review evidence identifies the authored mathematics, cited Lean source, and
notation conventions it covers. Saved bundles and review records make the comparison inspectable and allow
syntactic checks to identify missing or stale evidence when its inputs change. A successful citation lookup
or MathJax render must not be reported as that review evidence.

{informational} Selectors support inspection; the evidence checker validates
record structure, coverage of required inputs, and freshness. Human or agent
review still judges correspondence. Passing the checker does not establish
mathematical equivalence between the authored account and Lean.

{anchor}`meta.examples.coverage`
Every completed semantic example links to a Lean test of its intended behavior.
A proposed scenario whose semantics or test is unfinished uses
`:status: draft`; it is not presented as a checked example.
Authoring-syntax illustrations are ordinary prose and literal code;
they do not create additional semantic claims or evidence records.

{anchor}`meta.examples.evidence`
The source association, Lean proof check, and correspondence review are separate
checks. The preprocessor checks the association. Compiling the containing Lean
file checks the example under its imports, declarations, and assumptions; that
compilation is separate from rendering the book. Review checks that the example's
proposition and setup cover the behavior described by the Markdown, including
any stated preconditions and results. Neither a valid citation nor a successful
proof by itself establishes that correspondence or broader claim coverage.

{anchor}`meta.syntax.lean.mathematical_containers`
The shared mathematical notation writes an overbar over an element or category
for a finite ordered sequence, whether its Lean representation uses `List` or
`Array`. A finite map is written `K ⇀ V`, with no finiteness subscript. Map
domains, comprehensions, lookup, and update are defined where used. The notation
does not assert that Lean's list and array types are identical or erase any
required bounds or uniqueness conditions. Supporting representation details,
such as the proof field in `FiniteMap`, may remain only in Lean when their
mathematical meaning has been stated in the book.

{anchor}`meta.syntax.lean.alignment`
Authors align grammar definition symbols and alternative separators in one
column. Long constructor arguments can continue on separate lines aligned with
the first argument; rules place distinct premises on separate lines. These are
conventions for the authored LaTeX, not layouts inferred from Lean syntax.
