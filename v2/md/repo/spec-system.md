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
The tooling's implemented review contracts are themselves structured units in
[Implementation contracts](evidence-pilot.md#implementation-contracts). They cite
Rust symbols and tests and require the same recorded comparison as language units.
The remaining requirements in this reference chapter are migration work:

```{definition} meta.system.remaining_coverage
:status: draft

*Complete review coverage* requires every renderer and diagram requirement in
this chapter to have a review unit with implementation and test citations.
Mechanical execution results and proof assumptions must be recorded separately
from correspondence judgments.

The current checker validates review inputs and decisions. It does not yet retain
those mechanical results or cover every legacy requirement in this chapter.
```

This draft fails evidence validation until the coverage requirement is implemented
and reviewed. Reviews of the existing contracts cover those contracts, not every
renderer feature or every paragraph of this book.

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
remains a separate `just test-lean` invocation. The current evidence command does
not turn a recorded review into an assertion that Lean or Cargo was executed.

## Mathematics and Lean citations

{informational} The state grammar and operational semantics are authored in the
book, with citations relative to the configured Lean source root (`lean/` here). The declarations, examples, and
named theorems have been checked with Lean 4.35.0. That check establishes their
Lean statements, not correspondence with the book or any broader property.

### Independent mathematical account

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

{anchor}`meta.math.typesetting`
MathJax typesets the book's authored mathematics. The bodies of `{grammar}`,
`{judgment}`, and `{rule}` are raw LaTeX: the renderer supplies display-math
delimiters, and Markdown inside those bodies is not interpreted. The bodies of
`{definition}`, `{theorem}`, `{lemma}`, and `{example}` are Markdown, so authors use the same
explicit math delimiters as elsewhere in the book: `\\[` and `\\]` for display
math, or `\\(` and `\\)` for inline math. Heap diagrams render as SVG.
The preprocessor protects the contents of these explicit math spans from
Markdown escaping and smart punctuation. TeX row breaks, braces, underscores,
and primes therefore keep their mathematical meaning; literal code samples
are left untouched.

{anchor}`meta.math.runtime`
The book loads one pinned MathJax runtime through `theme/mathjax.js` for both
local previews and published pages. mdBook's built-in MathJax loader is disabled
so it cannot load a second runtime. Mathematical blocks retain their
authored line breaks and scroll horizontally when needed.

{informational} The current runtime is MathJax 4.1.3 with CommonHTML output and
the New Computer Modern math font. Its scripts and fonts load from a CDN, so
mathematical typesetting requires network access. The Markdown source and Lean
selectors remain available independently of MathJax.

{anchor}`meta.math.source_view`
Lean-backed mathematical blocks offer a Rendered/Lean selector, with Rendered
selected initially. Meta definitions with Rust citations offer Rendered/Rust.
A draft without citations has an identity header without source controls. Draft status remains visible in the header.
Rendered shows the authored notation or Markdown. Lean identifies
each citation and shows its extracted source. A definition or grammar may show
several declarations; a judgment shows its inductive declaration; a rule shows
the inductive header and selected constructor; a theorem or lemma shows its
named statement and complete proof. Each block has a header with its identity
on the left and the view selector on the right. A structured unit's opening-line
ID appears there as a shield and remains visible in either view. In legacy
Markdown blocks, leading anchors serve that presentation role. Legacy blocks
without a leading anchor show their kind, such as **Definition**, **Theorem**,
or **Grammar**. Diagram headers follow the same
layout with Rendered/Facts controls. Switching views supports inspection and
comparison, not an automatic correspondence check.

{anchor}`meta.lean.definitions.presentation`
The mathematical presentation may use conventional symbols and omit Lean's
implementation details under explicit notation conventions. The Lean view
retains the original declaration, including fields, proof arguments, and derived
instances. The renderer does not infer a mathematical grammar from these details.

### Selecting formalizations

{anchor}`meta.math.definition.selection`
A structured `{definition}` directive has its unit ID on the opening line and
one or more whitespace-separated `path:Name` citations in its `:lean:` option,
unless marked `:status: draft`. Its Markdown body introduces the
concept in prose and explicitly delimited mathematics. Each citation selects a
complete named Lean `def`, `abbrev`, `structure`, or `inductive` declaration;
requested order is preserved in one Rendered/Lean selector. A theorem, axiom,
anonymous example, or individual constructor is not a definition target.

For example, completion has an authored explanation and a directly inspectable
Lean definition. The following blocks are literal authoring illustrations, not
additional review units:

````text
```{definition} example.finished
:lean: Unique/State:Configuration.finished

A configuration is finished when its list of remaining statements is empty.
Its state may still contain objects and variables.
```
````

Completed semantic definitions have this source association, including when their
notation differs from Lean's. Their explanatory narrative and notation conventions belong
inside the unit or in explicit `:uses:` dependencies. This keeps the account
readable on its own and gives correspondence review a complete boundary.

{anchor}`meta.lean.definitions.selection`
A named inductive in a top-level `mutual` group can be selected individually.
Group delimiters and member headers start at column zero; each header ends in
`where` on its first line and its body is indented. Selection preserves the
complete member, with the enclosing source retained in evidence. Nested groups
and other mutual declaration kinds are rejected.

A structured `{grammar}` directive has its unit ID on the opening line and
one or more whitespace-separated `path:Name` citations in `:lean:`. Each identifies a type declaration, and requested
order is preserved in one shared Rendered/Lean selector. Its body supplies the
mathematical grammar. For example:

````text
```{grammar} example.places
:lean: Unique/Syntax:Place

\begin{array}{rcl}
p & ::= & x \mid p.f
\end{array}
```
````

This example uses \\(p\\) for a place, \\(x\\) for a variable name, and
\\(f\\) for a field name. A place is a variable or a field selected from
another place. A chapter defines these categories before using them in rules.

{anchor}`meta.math.judgment.selection`
A structured `{judgment}` directive has its unit ID on the opening line and
one `:lean: path:Name` citation identifying an inductive declaration. Its body supplies the authored mathematical
presentation of the judgment, including any desired argument types. It does not
insert all of the judgment's rules automatically.

{anchor}`meta.math.rule.selection`
A structured `{rule}` directive has its unit ID on the opening line and one
`:lean: path:Judgment.constructor` citation identifying an inductive constructor.
Its body supplies the authored inference rule. The author supplies any displayed
rule label as part of that notation.

For example, a judgment and one of its inference rules have separate citations:

````text
```{judgment} example.resolve
:lean: Unique/Step:Resolve

S \vdash p \Downarrow q : \alpha
```

```{rule} example.resolve_variable
:lean: Unique/Step:Resolve.variable
:uses: example.resolve

\frac{
  (x,\mathsf{some}(\alpha)) \in S.\mathsf{variables}
}{
  S \vdash x \Downarrow \mathsf{variable}(x) : \alpha
}
\;\text{ResolveVariable}
```
````

The judgment resolves source place \\(p\\) in state \\(S\\) to storage
location \\(q\\) holding object identity \\(\alpha\\). In the rule,
\\(x\\) is a variable name; \\(\mathsf{some}(\alpha)\\) denotes an
initialized slot. Its premise says that the variable store contains that binding.
Resolution reads the state without changing it.

{anchor}`meta.math.theorem.selection`
A structured `{theorem}` or `{lemma}` directive has its unit ID on the opening
line and one `:lean: path:Name` citation identifying a named Lean `theorem`. Its Markdown body states the
claim and its assumptions in prose and mathematics. The Lean view includes the selected theorem's statement and
complete proof body. A definition, axiom, or anonymous example is not a valid
target. Both directives cite the same Lean declaration kind; the distinction
between a theorem and a supporting lemma is the author's presentation choice.

````text
```{theorem} example.take_counter
:lean: Unique/Soundness:Take.next_id

Taking an object reference from a storage location leaves the object-identity
counter unchanged. Here \\(\mathsf{Take}(S,q,\alpha,S')\\) means taking
the reference to \\(\alpha\\) from location \\(q\\), yielding state
\\(S'\\).

\\[
\mathsf{Take}(S,q,\alpha,S')
\implies S'.\mathsf{nextId} = S.\mathsf{nextId}
\\]
```
````

The body supports ordinary Markdown, the book's roles, and heap or mathematical
directives. Use a longer enclosing fence when the body contains fenced blocks.
Definition, theorem, lemma, and example blocks cannot contain any of those four block kinds.

{anchor}`meta.math.theorem.validation`
The directive verifies that its citation selects a supported named theorem with
a proof body. The book build does not check that proof: compile the containing
Lean file to establish the theorem in its source context. Correspondence review
must separately check that the displayed claim preserves the Lean statement's
assumptions and conclusion, including quantifier scope and any hidden parameters.
The proof itself is left to Lean; correspondence review does not recheck tactics
or require a prose proof outline. A proposed theorem remains marked draft until
formalized and checked by Lean.
Neither its label nor mathematical notation establishes the result.

{anchor}`meta.lean.definitions.navigation`
Each Lean view identifies its source file and declaration or constructor name.
The path is relative to `preprocessor.dada.lean-source`, configured relative to
the book root (currently `lean`). A missing `.lean` extension is supplied.
Relative subdirectories are allowed; paths cannot escape this directory,
including through symlinks. Names must match the identifier literally written
in the declaration. Definition and theorem names may contain dot-separated,
nonempty identifier components, such as `FiniteMap.lookup`; inclusion does not
infer qualification from enclosing namespaces.

{informational} Structured directives follow MyST's argument and option layout:
the ID follows the directive name, then supported options precede a blank line
and the body. This is a supported subset, not a general MyST implementation.
Legacy blocks outside strict chapters still accept opening-line citations.
The unsupported `{lean.type}`, `{lean.judgment}`, and `{lean.rule}` directives
produce diagnostics directing authors to the corresponding fenced directives. Lean notation comments have no rendering effect.

{anchor}`meta.lean.definitions.extraction`
Source inclusion locates the selected declaration's kind, name, and complete
syntactic extent, including constructors and their fields. A matching string
inside a comment or another identifier does not identify a declaration.
For a rule, inclusion selects the named constructor and the inductive header.
This selection does not interpret constructor arguments or classify premises.
For a definition block, inclusion selects each complete declaration, including
its implementation body. For a theorem or lemma block, inclusion selects the
named theorem and its proof without including a neighboring declaration.

{informational} The source extractor supports `inductive`, `structure`, and
`abbrev` for type citations; definition citations additionally support `def`.
Theorem and lemma citations select `theorem` declarations. Declarations start at
column zero; continuation lines are indented. Type declarations' first line
contains `where` (or `:=` for an abbreviation). Definitions may have indented
signature continuations and use a `:=` body, a `where` body, or equation clauses.
A theorem's statement may span indented lines and must include its `:=` proof body. Sibling commands must
start at column zero, and commands nested within a selected proof are unsupported.
Nested comments and strings are masked when locating boundaries. This is textual extraction,
not Lean parsing or elaboration; attributes, mutual declarations, and namespace
resolution are not supported. Imports, namespaces, and section variables remain
source-file context, so an extracted declaration is not a standalone Lean file.

{anchor}`meta.lean.definitions.errors`
A missing file, missing or ambiguous declaration, or unsupported extraction form
fails the book build with a diagnostic identifying the citation and its target.
The processor must not silently omit a citation or show a partial extraction as
if it were complete.

{anchor}`meta.math.citations.validation`
The build rejects missing or ambiguous targets, wrong declaration kinds, missing
constructors, malformed directive arguments, and empty directive bodies.
These checks establish that the citations select supported source declarations.
They do not interpret binder types, classify premises, or check that an inductive
declaration returns `Prop`. MathJax processes mathematical syntax in the reader's
browser; the build does not check the authored notation as a Lean proposition.

{anchor}`meta.math.unsupported`
A Lean form outside the source extractor's supported style requires an extraction
extension or a source change before it can be cited. A new mathematical notation
requires only an authored LaTeX body and its explanation; there is no translation
from Lean that must recognize the notation.

### Notation and correspondence

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

{anchor}`meta.math.overline.braces`
Overbar expressions always use an enclosing group, as in `{\overline f}`.
The command must be immediately preceded by an opening brace and immediately
followed by a literal ASCII space; tabs and newlines do not satisfy the latter
condition. Punctuation following the expression belongs outside its closing
brace. The preprocessor rejects a violation of either adjacency condition with
a source path and line number. This lint checks raw Markdown, including literal
TeX illustrations that readers might copy; longer TeX command names are not
matches. A repository test checks every Markdown file under `v2/md/`, including
files not listed in the book's table of contents.

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

## Authoring syntax

{anchor}`meta.syntax.inline_and_block`
Inline content uses roles, such as `{anchor}` and `{anchor-ref}`.
Content that renders as a block uses a fenced directive: `{definition}`,
`{grammar}`, `{judgment}`, `{rule}`, `{theorem}`, `{lemma}`, `{example}`, or
`{heap}`. Ordinary language fences such as `lean`, `heap`, `grammar`, and `text`
remain literal code examples; they do not invoke a block renderer.


{anchor}`meta.syntax.anchors.roles`
Definitions, theorems, and lemmas have distinct presentation roles:

| Kind | Authoring form | Meaning |
| --- | --- | --- |
| Definition | Fenced `{definition}` with Lean citations | Introduces a concept or judgment and exposes its formalization. |
| Theorem | Fenced `{theorem}` with a Lean citation | States a result. |
| Lemma | Fenced `{lemma}` with a Lean citation | States a supporting result. |

`:status: draft` marks unfinished formalization independently of these kinds
and permits omitted source citations. It never marks a result as proved.

Structured blocks introduce their stable ID on the opening line, and show that
identity in the header. They do not need a second identifying anchor in their
body. Other chapters refer to those IDs with `{anchor-ref}`. IDs named by `:uses:`
identify context that belongs in the review packet even when it is not quoted.

Legacy inline roles register locations in the same global namespace. An
`{anchor}` is neutral outside definition or proof blocks and inherits the
surrounding kind inside one. In legacy blocks, leading identifying anchors move
into the header. A legacy inline anchor alone does not define a complete unit
for evidence validation.

Meta requirements use structured definition units with implementation and test
citations. Legacy requirements may retain neutral `{anchor}` markers until
migration. A label records the author's category; it does not establish
correspondence or certify that a result has been proved.

{anchor}`meta.syntax.anchors.inline`
Keep the anchor marker in the same paragraph as its claim (with no blank line
between them) so that the shield appears inline with the text.

{anchor}`meta.syntax.anchors.identity`
IDs are global and use ASCII letters, digits, dots, underscores, and hyphens,
beginning with a letter or digit. Bad IDs, duplicate definitions, and unresolved
references fail the build.

{anchor}`meta.syntax.anchors.rendering`
Defining markers become local shields labeled **definition** or neutral **anchor**.
An `{anchor}` inside a definition, theorem, or lemma body inherits that label.
References become shields labeled
**ref** linking to the defining chapter and fragment, including across nested
chapter directories. No shields.io network request is required.

{anchor}`meta.syntax.anchors.literal`
Markers in fenced or indented code, links, and HTML blocks remain literal, as do
escaped role prefixes and demonstrations using double-backtick code spans.
The processor implements these custom MyST-compatible roles, not a full MyST parser.

### Informational paragraphs

{anchor}`meta.syntax.informational`
A paragraph beginning with `{informational}` followed by a space renders with
an inline **Informational** label. The rest of the paragraph remains ordinary
Markdown, including links and emphasis. The marker creates no anchor or claim
identity. It explicitly separates rationale or commentary from normative claims.
Markers in code examples remain literal.

```text
{informational} This choice permits a JVM array implementation.
```

### Examples and Lean tests

{anchor}`meta.examples.coverage`
Every completed semantic example links to a Lean test of its intended behavior.
A proposed scenario whose semantics or test is unfinished uses
`:status: draft`; it is not presented as a checked example.
Authoring-syntax illustrations are ordinary prose and literal code;
they do not create additional semantic claims or evidence records.

{anchor}`meta.syntax.example`
A structured `{example}` directive has its unit ID on the opening line and
one `:lean: path:anchor` citation. Its body is authored Markdown describing the example. The Rendered/Lean
selector initially shows that Markdown with an **Example** label; the Lean view
identifies the citation and shows the selected test source. The structured
block's ID identifies the complete example. Paragraph-prefix
`{example}` is unsupported; examples require the fenced directive.

For example, the directive has this form:

````text
```{example} example.create_token
:lean: Unique/Examples:create_token

Declare an empty class `Token` and a class `Box` with one field `value`.
Starting with no objects or variables and the object-identity counter at zero,
execute `let t = new Token()`.

The result contains the fieldless `Token` object 0 and variable `t` referring
to it. The counter is 1, and no statements remain.
```
````

{anchor}`meta.examples.markdown`
The body supports ordinary Markdown paragraphs, lists, links, code, and math,
as well as the book's roles and heap or mathematical directives. Use a longer
outer fence when the body contains fenced blocks. Definition, theorem, lemma,
and example blocks cannot contain any of those four block kinds.

{anchor}`meta.examples.selection`
An example citation selects a region delimited by standalone Lean line comments
`-- ANCHOR: name` and `-- ANCHOR_END: name`. The region contains exactly one
top-level anonymous `example` proof, together with any comments and whitespace.
The `example` starts at column zero, its continuation lines are indented, and
the next command after the closing marker starts at column zero. A marker must
not cut off the proof or enclose another declaration, even an indented one.
The markers are excluded from the displayed source. The anchor identifies the
region within its file; it is not a Lean declaration name or a prose claim ID.
The path is relative to the configured `lean-source` directory, may include
subdirectories, and may omit `.lean`, as with mathematical citations.

For example, a source region demonstrating the marker syntax is:

```lean
-- ANCHOR: reflexivity
example (x : Nat) : x = x := by
  rfl
-- ANCHOR_END: reflexivity
```

{anchor}`meta.examples.validation`
The book build rejects missing files or anchors, duplicate or malformed anchor
regions, regions containing anything other than the supported anonymous example
form, malformed directive arguments, and empty bodies. Paths cannot escape the
configured source directory, including through symlinks. Source selection
preserves the test; it does not elaborate its proposition or proof.

{anchor}`meta.examples.evidence`
The source association, Lean proof check, and correspondence review are separate
checks. The preprocessor checks the association. Compiling the containing Lean
file checks the example under its imports, declarations, and assumptions; that
compilation is separate from rendering the book. Review checks that the example's
proposition and setup cover the behavior described by the Markdown, including
any stated preconditions and results. Neither a valid citation nor a successful
proof by itself establishes that correspondence or broader claim coverage.

### Mathematical grammars

{anchor}`meta.syntax.grammar.declarations`
A structured `{grammar}` block has an ID, one or more Lean declaration citations
in `:lean:`, and authored LaTeX in its body, as specified by
{anchor-ref}`meta.lean.definitions.selection`. Mathematical categories, constructor
notation, and side conditions are explained by the surrounding Markdown. They
do not need to reproduce Lean's surface syntax.

{anchor}`meta.syntax.grammar.validation`
A grammar block validates citation syntax, target existence, supported declaration
kinds, and a nonempty body. The build does not validate an independent algebraic
data-type language, resolve mathematical symbols, or establish correspondence
with Lean. The `{grammar}` body accepts authored LaTeX, not a separate
constructor-definition language.

{anchor}`meta.syntax.grammar.rendering`
The renderer gives the authored LaTeX to MathJax and preserves the cited Lean
source in the selector. LaTeX and source text are escaped for HTML. This is the
same presentation mechanism used for judgments and rules, with one shared
Rendered/Lean selector per block.

### Heap facts

The fact language renders object and reference diagrams. It also retains legacy
borrowing constructors as renderer syntax. Given and Shared do not define
borrowing, primitives, or arrays; the availability of those diagram forms does
not introduce them into either language. Use only forms whose meaning is
explained by the model being illustrated.

{anchor}`meta.syntax.heap.state`
A `{heap}` fenced directive describes one state, rather than a sequence of operations:

````text
```{heap}
vars = variables()
α = object(Point, "α")
β = primitive(22, "β")
vars.p = owned(α)
vars.b = uninitialized()
α.x = owned(β)
α.y = uninitialized()
```
````

{anchor}`meta.syntax.heap.nodes`
Nodes can be a variable-store group, objects, primitives, or arrays. A diagram
has at most one variable-store group; it may omit that group for an object-only
view. Owned, showned, and shlease references target objects, primitives, or arrays;
they cannot target the variable-store group. Unique leases target an owned or leased edge,
written `lease(α.f)`, `lease(vars.p)`, or `lease(items[0])`. Declare each node and slot only
once. Forward references are permitted. Unicode identifiers work; optional quoted
labels use JSON string escaping. Blank lines and lines beginning with `#` are
ignored. Arguments are comma-separated; quoted arguments can contain commas.

{anchor}`meta.syntax.heap.constructors`
The supported constructors and assignments are:

- `variables()` groups live variable slots under the label “Variables”;
  `variables("name")` overrides that label. The group is a presentation aid,
  not a heap object or a frame. In `vars.x`, the prefix names this group and
  `x` identifies the variable slot.
- `object(Point)` or `object(Point, "α")` declares a labeled aggregate.
- `primitive(22)` or `primitive(22, "β")` declares an opaque primitive label.
- `array(2)` or `array(2, "items")` declares a fixed number of slots.
- `vars.p = owned(α)` sets a variable slot; `items[0] = owned(β)` sets an array slot.
- Reference constructors are `owned`, `lease`, `showned`, and `shlease`.
  `leased` is an alias for `lease`; both require an edge target.
  `shared` is an alias for `shlease`, never inferred to mean `showned`.
- `uninitialized()` explicitly marks an empty slot. All array slots start empty.

{anchor}`meta.syntax.heap.validation`
The renderer rejects unknown targets, multiple variable-store groups, duplicate assignments, invalid projections,
and out-of-bounds indices. Lease targets must name an initialized owned or
leased edge; forward references to edges are permitted. Arrays in diagrams are limited to 64 slots for readable
output; that is a tooling limit, not a semantic array bound. The renderer accepts
ownership cycles and conflicting owners so that we can illustrate malformed
states. Structural validation is **not** validation of heap invariants.

{anchor}`meta.syntax.heap.rendering`
SVG diagrams preserve individual labeled references, with variables grouped on the
left when reachable objects allow it. A Rendered/Facts selector switches each diagram independently between its SVG
and its source facts, with Rendered selected initially. The SVG description also
exposes the input. Layout is deterministic, but does not add support
edges or infer lease provenance. Explicit lease targets are rendered as
junctions on the named edge. See {anchor-ref}`meta.rendering.faithfulness`.

### Checking the authoring claims

The preprocessor tests exercise these claims with valid examples and rejection
cases. `tests/book.rs` covers roles, links, literal contexts, and fenced-block
integration; `src/lean.rs` covers source extraction and citation-backed
mathematical blocks and examples; `src/graph.rs` covers heap facts. These are supporting tests, not an automated
claim-coverage certification. Structured units additionally expose implementation
and test citations to the evidence inventory. The configured scope remains
explicit; legacy inline requirements do not acquire reviewed status merely by
appearing in this chapter.

{anchor}`meta.syntax.heap.routing`
Diagram edges use horizontal and vertical segments, ending in dots. Object-targeting edges enter along the left boundary;
lease edges join their explicitly named supporting edge. The router seeks short paths with few bends through
corridors around object and variable-store boxes, including gaps within a column.
It avoids box interiors; it does not guarantee that edge paths or labels never
overlap. Lease junctions still identify the explicitly named supporting place.

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
