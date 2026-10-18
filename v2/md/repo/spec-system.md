# Specification system design

This chapter specifies the system connecting narrative, definitions, formal
obligations, code, and evidence. The Rust `mdbook-dada` preprocessor currently
indexes anchor definitions and references and renders fact-based heap diagrams.
Authored mathematical views and Lean source citations are implemented. Definition
blocks pair Markdown explanations with named Lean declarations. Theorem and lemma
blocks pair Markdown statements and proof outlines with named Lean proofs;
example blocks pair Markdown with anchored Lean tests. The book
build does not check proofs or mathematical correspondence; claim-content
extraction, a general claim/evidence inventory, and the review store remain planned. A shield
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
primitive/aggregate/array creation, path permissions, and place operations.
Checked theorems establish ownership preservation for these transitions and
effects. Reference invalidation, the full static checker, and the review schema
remain open. Further implementation should start with
a small end-to-end example and retain the evidence distinctions above.


## Mathematics and Lean citations

{informational} The state grammar and operational semantics are authored in the
book, with citations to files under `lean/`. The declarations, examples, and
named theorems have been checked with Lean 4.35.0. That check establishes their
Lean statements, not correspondence with the book or any broader property.

### Independent mathematical account

{anchor}`meta.math.source`
A grammar, judgment, or rule block contains authored mathematical notation and
citations into Lean. A definition block contains an authored Markdown explanation
with citations to its Lean formalization. A theorem or lemma block contains an
authored Markdown statement and optional proof outline, with a citation to its
Lean proof. These accounts
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
Every mathematical block offers a Rendered/Lean selector, with Rendered selected
initially. Rendered shows the authored notation or Markdown. Lean identifies
each citation and shows its extracted source. A definition or grammar may show
several declarations; a judgment shows its inductive declaration; a rule shows
the inductive header and selected constructor; a theorem or lemma shows its
named statement and complete proof. Each block has a header with its identity
on the left and the view selector on the right. A leading anchor in a Markdown
block appears there as a shield, replacing the plain kind label; it remains
visible in either view. Blocks without a leading anchor show their kind, such
as **Definition**, **Theorem**, or **Grammar**. Diagram headers follow the same
layout with Rendered/Facts controls. Switching views supports inspection and
comparison, not an automatic correspondence check.

{anchor}`meta.lean.definitions.presentation`
The mathematical presentation may use conventional symbols and omit Lean's
implementation details under explicit notation conventions. The Lean view
retains the original declaration, including fields, proof arguments, and derived
instances. The renderer does not infer a mathematical grammar from these details.

### Selecting formalizations

{anchor}`meta.math.definition.selection`
A fenced `{definition}` directive takes one or more whitespace-separated
`path:Name` citations on its opening line. Its Markdown body introduces the
concept in prose and explicitly delimited mathematics. Each citation selects a
complete named Lean `def`, `abbrev`, `structure`, or `inductive` declaration;
requested order is preserved in one Rendered/Lean selector. A theorem, axiom,
anonymous example, or individual constructor is not a definition target.

For example, slot lookup has an authored explanation and a directly inspectable
Lean definition:

````text
```{definition} Places:readSlot
{anchor}`heap.example.slot_lookup`
We write \\(S(p)=s\\) when place \\(p\\) exists in state \\(S\\) and
contains slot \\(s\\). Lookup at an absent variable, missing field, or
out-of-bounds element is undefined.

In Lean, `readSlot S p = some s` expresses successful lookup; `none` expresses
undefined lookup. An uninitialized slot is still a successful lookup.
```
````

Semantic definitions have this source association, including when their notation
differs from Lean's. Explanatory narrative or notation reminders may remain
ordinary prose; they do not receive a standalone Definition label without a
formalization citation. A grammar or judgment already associates its notation
with source, so adjacent prose need not duplicate that selector.

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

For example, a judgment and one of its inference rules have separate citations:

````text
```{judgment} Heap:Step
S \xrightarrow{\omega} S'
```

```{rule} Heap:Step.allocVariable
\frac{
  \begin{gathered}
    x \notin \operatorname{dom}(V) \\
    V' = (x : \bot) :: V
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
name the store \\(V^{\prime}\\) after pushing the new slot. The operations chapter
explains stack order and the separate obligation to prevent later allocations
from reviving references to retired bindings.

{anchor}`meta.math.theorem.selection`
A fenced `{theorem}` or `{lemma}` directive takes one opening-line argument,
`path:Name`, identifying a named Lean `theorem`. Its Markdown body states the
claim and its assumptions in prose and mathematics, and may give a high-level
proof outline. The Lean view includes the selected theorem's statement and
complete proof body. A definition, axiom, or anonymous example is not a valid
target. Both directives cite the same Lean declaration kind; the distinction
between a theorem and a supporting lemma is the author's presentation choice.

````text
```{theorem} Heap:deallocVariable_requires_top
{anchor}`heap.example.deallocation_top`
Deallocation can remove only the newest live variable.

\\[
S \xrightarrow{\mathsf{deallocVariable}(x)} S'
\implies \operatorname{top}(V) = x
\\]

**Proof outline.** The deallocation rule removes an uninitialized slot
at the head of the variable store.
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
assumptions and conclusion, and that the prose proof outline describes valid
reasoning for that claim. The outline is an explanation, not an additional
machine-checked proof. A candidate property without a checked proof is a proof
obligation; giving it mathematical notation does not establish it.

{anchor}`meta.lean.definitions.navigation`
Each Lean view identifies its source file and declaration or constructor name.
The path is relative to `preprocessor.dada.lean-source`, configured relative to
the book root (currently `lean`). A missing `.lean` extension is supplied.
Relative subdirectories are allowed; paths cannot escape this directory,
including through symlinks. Names must match the identifier literally written
in the declaration. Definition and theorem names may contain dot-separated,
nonempty identifier components, such as `FiniteMap.lookup`; inclusion does not
infer qualification from enclosing namespaces.

{informational} These directives follow MyST's convention of arguments after
the directive name on the opening fence. General MyST options are not implemented.
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
The common set of primitive values is fixed for the model and implicit in the
mathematical definitions and judgments. Authored notation may also abbreviate
terms and suppress proof terms under stated conventions. Conditions represented
by proof arguments remain explicit: hiding the proof of freshness or distinctness
does not remove that condition. Equations introducing intermediate names must
preserve their dependencies and scopes.

{anchor}`meta.math.heap_representation`
The heap's mathematical definitions stand on their own, with Lean declarations
available for comparison through their citations. The mathematical slot
\\(\bot\\) corresponds to `Slot.uninitialized`; using a reference \\(r\\) as
a slot abbreviates `Slot.initialized r`. The common primitive set \\(P\\)
corresponds to Lean's `Primitive` parameter. Mathematical sequences and finite
maps abstract their Lean representations, but the variable store retains an
additional ordering: its `FiniteMap` entries record allocation order, newest
first. Treating that store as a map must not erase the order used by variable
deallocation. Proof fields in these representations establish conditions such
as distinct keys; omitting the proof term from notation does not omit its
condition.

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

For example, the operations chapter explains the state pair and fresh map extension
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
Inline content uses roles, such as `{obligation}`, `{anchor}`, and `{anchor-ref}`.
Content that renders as a block uses a fenced directive: `{definition}`,
`{grammar}`, `{judgment}`, `{rule}`, `{theorem}`, `{lemma}`, `{example}`, or
`{heap}`. Ordinary language fences such as `lean`, `heap`, `grammar`, and `text`
remain literal code examples; they do not invoke a block renderer.


{anchor}`meta.syntax.anchors.roles`
Definitions, theorems, lemmas, and proof obligations have distinct presentation
roles:

| Kind | Authoring form | Meaning |
| --- | --- | --- |
| Definition | Fenced `{definition}` with Lean citations | Introduces a concept and exposes its formalization. |
| Theorem | Fenced `{theorem}` with a Lean citation | States a proved result and can explain its proof. |
| Lemma | Fenced `{lemma}` with a Lean citation | States a proved supporting result and can explain its proof. |
| Proof obligation | Inline `{obligation}` role with an ID | States a property still to be established. |

The inline roles register stable IDs in the same namespace. An `{anchor}` role
registers an ID without choosing a semantic category: it is neutral outside
definition or proof blocks, and inherits the surrounding definition, theorem,
or lemma kind inside one. Those blocks do not introduce IDs automatically; put
an `{anchor}` role in the body to give the definition or statement a stable
identity. Use the fenced definition form to include the associated Lean source.
Put a block's identifying anchor at the start of its body to display the shield
in its header. Consecutive leading anchors share that header. A leading example
anchor uses the **Example** label. Anchors introduced later in the body stay
with their prose; later example anchors remain neutral.

The slot-lookup illustration above shows how to define an ID such as
`heap.example.slot_lookup`. Other chapters can refer to that ID with `{anchor-ref}`. Proof obligations use an inline
role because their formalization or proof is unfinished:

```text
{obligation}`heap.example.obligation`
The property still to be proved goes here.

See {anchor-ref}`heap.example.slot_lookup` and
{anchor-ref}`heap.example.obligation`.
```

Meta requirements and other claims without one of these four semantic roles can
use neutral `{anchor}` markers. A label records the author's category; it does
not establish correspondence or certify a proof obligation as completed.

{anchor}`meta.syntax.anchors.inline`
Keep the anchor marker in the same paragraph as its claim (with no blank line
between them) so that the shield appears inline with the text.

{anchor}`meta.syntax.anchors.identity`
IDs are global and use ASCII letters, digits, dots, underscores, and hyphens,
beginning with a letter or digit. Bad IDs, duplicate definitions, and unresolved
references fail the build.

{anchor}`meta.syntax.anchors.rendering`
Defining markers become local shields labeled by their role: **definition**,
**proof obligation**, or neutral **anchor**. An `{anchor}` inside a definition,
theorem, or lemma body is labeled **definition**, **theorem**, or **lemma**. References become shields labeled
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
Every semantic example presented as an example links to a Lean test of its
intended behavior. A proposed scenario whose semantics or test is unfinished is
explicitly labeled proposed or pending, rather than presented as a checked
example. Authoring-syntax illustrations are ordinary prose and literal code;
they do not claim to test the heap semantics.

{anchor}`meta.syntax.example`
A fenced `{example}` directive takes one `path:anchor` citation on its opening
line. Its body is authored Markdown describing the example. The Rendered/Lean
selector initially shows that Markdown with an **Example** label; the Lean view
identifies the citation and shows the selected test source. Like an informational
paragraph, an example creates no claim identity of its own. Paragraph-prefix
`{example}` is unsupported; examples require the fenced directive.

For example, the directive has this form:

````text
```{example} Heap:nested_variables
Allocate an outer variable, then an inner variable. Deallocate the inner
variable while its slot is still uninitialized.

The resulting variable store contains only the uninitialized outer variable.
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
A `{grammar}` block has one or more Lean declaration citations on the opening
line and authored LaTeX in its body, as specified by
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
mathematical blocks and examples; `src/graph.rs` covers heap facts. These are supporting tests, not an automated
claim-coverage certification. A general machine-readable claim/evidence inventory
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
