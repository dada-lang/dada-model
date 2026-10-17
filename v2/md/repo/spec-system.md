# Specification system design

This chapter specifies the system connecting narrative, definitions, formal
obligations, code, and evidence. The Rust `mdbook-dada` preprocessor currently
indexes anchor definitions and references and renders fact-based heap diagrams.
Authored mathematical views and Lean source citations are implemented. The book
build does not check proofs or mathematical correspondence; claim-content
extraction, evidence associations, and the review store remain planned. A shield
identifies a claim; it does not certify it.

{anchor}`meta.anchors.identity`
Each named claim has a unique identity and one defining source location. References
and generated views resolve to that definition. Missing or ambiguous identities
are reported as errors rather than silently omitted.

{anchor}`meta.anchors.content`
The system defines explicit boundaries for each claim's complete content,
including qualifications and examples within those boundaries. Rendering and
review use that same content. Claim-content boundaries remain to be implemented. The current processor
indexes only the definition marker, not the prose that follows it.

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
policy. Changes affecting those inputs require renewed review. Source line-number
movement alone does not change the meaning of a review input.

Changing the definition of `live`, for example, can invalidate review even when a
theorem's displayed statement is unchanged. A change confined to proof technique
ordinarily requires proof checking without renewed correspondence review when
meaning and assumptions remain unchanged. How to identify the relevant dependency
set is an implementation question, not permission to omit it silently.

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
checked proof remain distinct evidence. Explicit pending work must remain visible
even if a structural check accepts it as accounted for.

{anchor}`meta.proofs.assumptions`
Evidence presented as a checked proof identifies its proposition, checked source
version, and assumptions, including admitted results or additional axioms.
The system applies an explicit policy to which assumptions are permitted; merely
building a Lean project is not enough to label every obligation proved.

{anchor}`meta.rendering.faithfulness`
Mathematical views render the notation authored in the Markdown, and Lean views
extract their cited source. Graph renderings derive from explicit state facts;
layout hints do not silently add semantic relationships. Readers can inspect the
formalization associated with a mathematical view and the facts underlying a
diagram. Extraction preserves the cited source; correspondence between authored
mathematics and that source is a separate review obligation.

The Markdown supplies a self-contained mathematical account. Its definitions and
explanations can be read without opening the Lean files, whose citations identify
associated formalizations for comparison.

{anchor}`meta.system.self_specification`
The specification tooling's own requirements participate in its claim, evidence,
and review system. Being a meta claim does not exempt a requirement from tracking
implementation, tests, or known gaps.

## Implementation direction

The Rust library in `v2/mdbook-dada` supplies the current book processing.
A future shared inventory will also support verification commands. Lean source
contains state declarations, variable allocation and deallocation transitions,
and checked lemmas about that slice. Other transitions, ownership
proofs, dependency tracking, and the review schema remain open. Further implementation should start with
a small end-to-end example and retain the evidence distinctions above.


## Mathematics and Lean citations

{informational} The state grammar and operational semantics are authored in the
book, with citations to `lean/Heap.lean`. The declarations and variable-lifecycle
lemmas have been checked with Lean 4.35.0. That check does not establish
correspondence with the book or the broader heap invariants.

### Independent mathematical account

{anchor}`meta.math.source`
A grammar, judgment, or rule block contains authored mathematical notation and
one or more citations into Lean. The mathematics is part of the Markdown
specification and stands on its own, with its symbols and assumptions explained
in the book. The preprocessor renders it and extracts the cited source; it does
not derive mathematics from Lean.

{anchor}`meta.lean.definitions.source`
Lean files contain the formal declarations cited by the book. The mathematical
account and its Lean formalization are maintained independently and compared
through explicit correspondence review. Neither version automatically prevails
in a discrepancy; resolving it can change either view or the intended design,
as in {anchor-ref}`meta.reviews.correspondence`.

{anchor}`meta.math.typesetting`
MathJax typesets authored grammar, judgment, and inference-rule notation. Each
mathematical directive's body is LaTeX; the renderer supplies display-math
delimiters and escapes the body for HTML. Authors do not include `\[` and `\]`,
and Markdown inside the body is not interpreted. Heap diagrams continue to
render as SVG.

{informational} mdBook's MathJax integration loads MathJax from a CDN, so
mathematical typesetting requires network access. The Markdown source and Lean
selectors remain available independently of MathJax.

{anchor}`meta.math.source_view`
Every mathematical block offers a Rendered/Lean selector, with Rendered selected
initially. Rendered shows the authored notation. Lean identifies each citation
and shows its extracted source. A grammar may show several declarations; a
judgment shows its inductive declaration; a rule shows the inductive header and
selected constructor. Switching views supports inspection and comparison, not
an automatic correspondence check.

{anchor}`meta.lean.definitions.presentation`
The mathematical presentation may use conventional symbols and omit Lean's
implementation details under explicit notation conventions. The Lean view
retains the original declaration, including fields, proof arguments, and derived
instances. The renderer does not infer a mathematical grammar from these details.

### Selecting formalizations

{anchor}`meta.lean.definitions.selection`
A fenced `{grammar}` directive takes one or more whitespace-separated `path:Name`
citations on its opening line. Each identifies a type declaration, and requested
order is preserved in one shared Rendered/Lean selector. Its body supplies the
mathematical grammar. For example:

````text
```{grammar} Heap:Slot Heap:Reference
\begin{array}{rcl}
s & ::= & \bot \mid r \\
r & ::= & \mathsf{owned}(\alpha) \mid \mathsf{leased}(p) \\
  & \mid & \mathsf{showned}(\alpha) \mid \mathsf{shlease}(\alpha)
\end{array}
```
````

This example uses \\(s\\) for a slot, \\(r\\) for a reference, \\(\alpha\\) for
an object ID, and \\(p\\) for a place. Here \\(\bot\\) denotes an
uninitialized slot; writing \\(r\\) as a slot abbreviates the initialized-slot
wrapper. A chapter defines these categories
before using them in rules.

{anchor}`meta.math.judgment.selection`
A fenced `{judgment}` directive takes one opening-line argument, `path:Name`,
identifying an inductive declaration. Its body supplies the authored mathematical
presentation of the judgment, including any desired argument types. It does not
insert all of the judgment's rules automatically.

{anchor}`meta.math.rule.selection`
A fenced `{rule}` directive takes one opening-line argument,
`path:Judgment.constructor`, identifying a constructor of an inductive declaration.
Its body supplies the authored inference rule. The author supplies any displayed
rule label as part of that notation.

{example} A judgment and one of its inference rules have separate citations:

````text
```{judgment} Heap:Step
S \xrightarrow{\omega} S'
```

```{rule} Heap:Step.allocVariable
\frac{
  \begin{gathered}
    x \notin \operatorname{dom}(V) \\
    V' = V[x \mapsto \bot]
  \end{gathered}
}{
  \langle O,V \rangle
  \xrightarrow{\mathsf{allocVariable}(x)}
  \langle O,V' \rangle
}
\;\text{AllocVariable}
```
````

This example uses \\(S\\) for a state, \\(\omega\\) for an operation,
\\(O\\) for an object map, \\(V\\) for the variable store, and \\(x\\) for a
runtime variable identity. The premises require an unallocated identity and
name the extended store \\(V^{\prime}\\). The operations chapter explains fresh
map insertion and the separate lifetime-freshness obligation on the execution
layer.

{anchor}`meta.lean.definitions.navigation`
Each Lean view identifies its source file and declaration or constructor name.
The path is relative to `preprocessor.dada.lean-source`, configured relative to
the book root (currently `lean`). A missing `.lean` extension is supplied.
Relative subdirectories are allowed; paths cannot escape this directory,
including through symlinks. Declaration and constructor names are simple,
unqualified names.

{informational} These directives follow MyST's convention of arguments after
the directive name on the opening fence. General MyST options are not implemented.
The old `{lean.type}`, `{lean.judgment}`, and `{lean.rule}` directives are rejected
with migration diagnostics. Lean notation comments have no rendering effect.

{anchor}`meta.lean.definitions.extraction`
Source inclusion locates the selected declaration's kind, name, and complete
syntactic extent, including constructors and their fields. A matching string
inside a comment or another identifier does not identify a declaration.
For a rule, inclusion selects the named constructor and the inductive header.
This selection does not interpret constructor arguments or classify premises.

{informational} The source extractor supports `inductive`, `structure`, and
`abbrev`. Declarations start at column zero; continuation lines are indented.
The first line contains `where` (or `:=` for an abbreviation). Nested comments
and strings are masked when locating boundaries. This is textual extraction,
not Lean parsing or elaboration; attributes, mutual declarations, and qualified
selection are not supported. Imports, namespaces, and section variables remain
source-file context, so an extracted declaration is not a standalone Lean file.

{anchor}`meta.lean.definitions.errors`
A missing file, missing or ambiguous declaration, or unsupported extraction form
fails the book build with a diagnostic identifying the citation and its target.
The processor must not silently omit a citation or show a partial extraction as
if it were complete.

{anchor}`meta.math.citations.validation`
The build rejects missing or ambiguous targets, wrong declaration kinds, missing
constructors, malformed directive arguments, and empty mathematical bodies.
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

{anchor}`meta.math.abbreviations`
The common set of primitive values is fixed for the model and implicit in the
mathematical definitions and judgments. Authored notation may also abbreviate
terms and suppress proof terms under stated conventions. Conditions represented
by proof arguments remain explicit: hiding the proof of freshness or distinctness
does not remove that condition. Equations introducing intermediate names must
preserve their dependencies and scopes.

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

{example} The operations chapter explains the state pair and fresh map extension
used in its variable-allocation rule. These are abbreviations
for the cited Lean constructors and helper applications, with proof terms
suppressed. Their meaning is explained in the Markdown rather than reconstructed
by the renderer.

{anchor}`meta.math.correspondence.evidence`
Review evidence identifies the authored mathematics, cited Lean source, and
notation conventions it covers. Later scripts may provide additional evidence
or identify stale reviews when those inputs change. A successful citation lookup
or MathJax render must not be reported as that review evidence.

{informational} The Rendered/Lean selector and citation validation are
implemented. Automatic correspondence checking, saved review records, and scripts
collecting correspondence evidence remain future work. Current tests cover
directive syntax, source selection, literal contexts, and HTML escaping. They do
not establish equivalence between authored mathematics and Lean.

## Authoring syntax

{anchor}`meta.syntax.inline_and_block`
Inline content uses roles, such as `{anchor}` and `{anchor-ref}`. Content that
renders as a block uses a fenced directive: `{grammar}`, `{judgment}`, `{rule}`,
or `{heap}`. Ordinary language fences such as `lean`, `heap`, `grammar`, and
`text` remain literal code examples; they do not invoke a block renderer.


{anchor}`meta.syntax.anchors.roles`
Define an anchor with a MyST-style role, and refer to it from any chapter:

```text
{anchor}`heap.example`
The English claim goes here.

See {anchor-ref}`heap.example`.
```

{anchor}`meta.syntax.anchors.inline`
Keep the anchor marker in the same paragraph as its claim (with no blank line
between them) so that the shield appears inline with the text.

{anchor}`meta.syntax.anchors.identity`
IDs are global and use ASCII letters, digits, dots, underscores, and hyphens,
beginning with a letter or digit. Bad IDs, duplicate definitions, and unresolved
references fail the build.

{anchor}`meta.syntax.anchors.rendering`
Definitions become local shields labeled `spec`; references become shields
labeled `ref` linking to the defining chapter and fragment, including across
nested chapter directories. No shields.io network request is required.

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

{anchor}`meta.syntax.example`
A paragraph beginning with `{example}` followed by a space renders with an
inline **Example** label. Its content remains ordinary Markdown. Like
`{informational}`, it creates no claim identity and stays literal in code blocks.
Use it to distinguish concrete instances from general definitions and rules.

### Mathematical grammars

{anchor}`meta.syntax.grammar.declarations`
A `{grammar}` block has one or more Lean declaration citations on the opening
line and authored LaTeX in its body, as specified by
{anchor-ref}`meta.lean.definitions.selection`. Mathematical categories, constructor
notation, and side conditions are explained by the surrounding Markdown. They
do not need to reproduce Lean's surface syntax.

{anchor}`meta.syntax.grammar.validation`
A grammar block validates citation syntax, target existence, supported declaration
kinds, and a nonempty body. The build does not validate an independent algebraic
data-type language, resolve mathematical symbols, or establish correspondence
with Lean. The former constructor DSL and its brace or angle-bracket syntax are
no longer an input language for `{grammar}`.

{anchor}`meta.syntax.grammar.rendering`
The renderer gives the authored LaTeX to MathJax and preserves the cited Lean
source in the selector. LaTeX and source text are escaped for HTML. This is the
same presentation mechanism used for judgments and rules, with one shared
Rendered/Lean selector per block.

### Heap facts

{anchor}`meta.syntax.heap.state`
A `{heap}` fenced directive describes one state, rather than a sequence of operations:

````text
```{heap}
vars = variables()
α = object(Point, "α")
β = primitive(22, "β")
vars.p = owned(α)
vars.b = shared(α)
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
mathematical blocks; `src/graph.rs` covers heap facts. These are supporting tests, not an automated
claim-coverage certification. A machine-readable evidence association system
remains future work.

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
