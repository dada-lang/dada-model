# Specification system design

This chapter specifies the system connecting narrative, definitions, formal
obligations, code, and evidence. The Rust `mdbook-dada` preprocessor currently
indexes anchor definitions and references and renders fact-based heap diagrams.
Lean declaration inclusion is implemented; proof checking, claim-content
extraction, evidence associations, and the review store remain planned. A shield identifies a claim; it does not certify it.

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
Included definitions and their local documentation come from their identified
sources. Graph renderings derive from explicit state facts; layout hints do not
silently add semantic relationships. Readers can inspect the sources underlying
a rendered definition, diagram, or evidence view.

The book supplies the narrative and can present these artifacts in a different
order from their source modules without maintaining duplicate definitions.

{anchor}`meta.system.self_specification`
The specification tooling's own requirements participate in its claim, evidence,
and review system. Being a meta claim does not exempt a requirement from tracking
implementation, tests, or known gaps.

## Implementation direction

The Rust library in `v2/mdbook-dada` supplies the current book processing.
A future shared inventory will also support verification commands. Lean source now contains the initial state declarations. Executable transitions,
proofs, dependency tracking, and the review schema remain open. Further implementation should start with
a small end-to-end example and retain the evidence distinctions above.


## Lean definitions in the book

{informational} The preprocessor implements `{lean.type}` for a restricted Lean declaration
style. The state page now includes `lean/Heap.lean`; its declarations have been
checked with Lean 4.35.0. This checks the declarations, not the prose claims or
heap transition properties.

{anchor}`meta.lean.definitions.source`
A modeled type's canonical declaration resides in a Lean source file. The book
includes that declaration from its source rather than maintaining a second,
manually synchronized definition in the book's grammar notation.

{informational} Canonical here identifies the source of the displayed definition.
It does not make Lean the authority on design intent: discrepancies between a
Lean definition and the English specification still require discussion, as in
{anchor-ref}`meta.reviews.correspondence`.

{anchor}`meta.lean.definitions.selection`
The fenced `{lean.type}` directive selects one or more declarations. Each
nonempty line is `path:Name`; files may differ, and requested order is preserved.
One group has one Grammar/Lean selector. For example:

````text
```{lean.type}
Heap.lean:ObjectId
Heap.lean:Place
```
````

The path identifies a Lean source file beneath the book's configured Lean source
directory; a missing `.lean` extension is supplied. Relative subdirectories are
allowed. The declaration name identifies the requested definition within that
file. `preprocessor.dada.lean-source` configures the directory relative to the
book root (currently `lean`). The old inline role is rejected. Paths cannot
escape this directory, including through symlinks. Names are simple and
unqualified, and must identify exactly one supported declaration in the file.

{anchor}`meta.lean.definitions.extraction`
Inclusion recognizes the selected declaration's kind, name, and complete syntactic
extent. For an inductive type, this includes its parameters and every constructor
with its fields. A matching string inside a comment or another identifier does
not identify a declaration. Extraction must account for supported Lean type
forms, rather than assuming every declaration begins with `inductive`.

{informational} The first implementation supports `inductive`, `structure`, and
`abbrev`. Declarations start at column zero; continuation lines are indented.
The first line contains `where` (or `:=` for an abbreviation). Nested comments
and strings are masked when locating boundaries. This is a restricted source
extractor, not Lean's parser; attributes, mutual declarations, and qualified
selection are not supported. Imports, namespaces, and section variables remain
source-file context, so an extracted declaration is not a standalone Lean file.

{anchor}`meta.lean.definitions.errors`
A missing file, missing or ambiguous declaration, or unsupported declaration
form fails the book build with a diagnostic identifying the inclusion and its
target. The processor must not silently omit a definition or display a partial
extraction as if it were complete.

{anchor}`meta.lean.definitions.presentation`
The default Grammar view renders recognized structures, inductive constructors,
and simple aliases compactly, retaining Lean identifiers and proof fields.
Aliases are explicitly labelled. Derived instances remain in the Lean view.
Unrecognized compact shapes fall back to Lean with an explanation. The Lean
selector reveals the extracted source with syntax highlighting. Presentation changes do not introduce an independently maintained type
definition.

{anchor}`meta.lean.definitions.navigation`
Each included declaration identifies its source file and declaration name so
that readers can locate the definition used by the book.

{informational} The selector changes presentation only. Extraction and
rendering alone are not evidence that Lean accepted the source or that it matches
the intended design; those are separate checks.

## Authoring syntax

{anchor}`meta.syntax.inline_and_block`
Inline content uses roles, such as `{anchor}` and `{anchor-ref}`. Content that
renders as a block uses a fenced directive: `{lean.type}`, `{heap}`, or
`{grammar}`. Ordinary language fences such as `lean`, `heap`, `grammar`, and
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

### Data definitions

{anchor}`meta.syntax.grammar.declarations`
A `{grammar}` fenced directive contains one or more named data definitions. Each
ends with `;`. A definition has one or more constructors, separated by `|`.
A single-constructor definition uses the same notation: `Frame = Frame(...)`. Constructor payloads use
parentheses and named, typed fields. Fields are comma-separated; a trailing
comma is allowed. Constructors with no fields are allowed. There is no separate record syntax.

````text
```{grammar}
// The payload type is supplied by the client.
Value<P> = Empty | Present(value: P);
Store<P> = Store(values: Map<Key, Value<P>>);
```
````

{anchor}`meta.syntax.grammar.production_rules`
The concrete syntax of a `{grammar}` directive is defined by these EBNF productions.
Quoted strings are literal tokens; `?` means optional, `*` means zero or more,
and `+` means one or more. Parentheses group EBNF expressions. The entire block
must match `document`.

```ebnf
document       = definition+ ;
definition     = comment* identifier parameters? "=" constructor
                 ("|" constructor)* ";" ;
parameters     = "<" identifier ("," identifier)* ">" ;
constructor    = identifier ("(" fields? ")")? ;
fields         = field ("," field)* ","? ;
field          = identifier ":" type ;
type           = identifier ("<" type ("," type)* ">")? ;
```

{anchor}`meta.syntax.grammar.tokens`
Whitespace is ignored between tokens. An identifier is a maximal sequence whose
first character satisfies Rust's `char::is_alphabetic` or is `_`, and whose
remaining characters satisfy `char::is_alphanumeric` or are `_`. A comment starts
with `//` and runs to the end of the line (or input). The punctuation tokens are
`<`, `>`, `=`, `|`, `(`, `)`, `,`, `:`, and `;`. Other characters are rejected.
Comments remain tokens, so the productions allow them only before definitions.

{informational} This EBNF describes the concrete notation; the `grammar` blocks
elsewhere describe data types. The preprocessor implements the EBNF with a
handwritten parser, rather than generating a parser from this block. The
uniqueness checks in {anchor-ref}`meta.syntax.grammar.validation` apply in addition
to these productions. Tests cover accepted constructors and rejection of the
removed brace syntax; they do not constitute a proof of parser–grammar equivalence.

{anchor}`meta.syntax.grammar.types`
Definition names may declare parameters in angle brackets. Field types are
names with optional, recursively nested type arguments, such as
`Map<ObjectId, Object<Primitive>>`. Identifiers begin with a Unicode letter or
underscore and continue with letters, digits, or underscores. Whitespace and
line breaks separate tokens but do not delimit definitions. Referenced type names
may be external; this notation does not check name resolution, type arity,
parameter scope, or correspondence with Lean.

{anchor}`meta.syntax.grammar.comments`
`//` starts a plain-text comment extending to the end of the line. Comments
are permitted before a definition and attach to that next definition. Comments
inside a definition or left without a following definition are rejected.
Comment text is escaped and displayed as documentation; it is not interpreted
as HTML, Markdown, or a claim about the model.

{anchor}`meta.syntax.grammar.validation`
Malformed tokens, incomplete definitions, untyped fields, and repeated definition
names within a block fail the build. Parameter names within a definition,
constructor names within a sum, and field names within a constructor
must each be distinct. Definitions in separate blocks have independent namespaces.
These checks validate notation, not heap invariants or proof obligations.

{anchor}`meta.syntax.grammar.rendering`
The renderer displays compact grammar equations with `=` and `|` and named constructor arguments. Documentation comments precede their definitions. Labels and types are escaped for
HTML. An expandable source panel preserves the original block so that the reader
can inspect the notation behind the presentation.

### Heap facts

{anchor}`meta.syntax.heap.state`
A `{heap}` fenced directive describes one state, rather than a sequence of operations:

````text
```{heap}
main = frame()
α = object(Point, "α")
β = primitive(22, "β")
main.p = owned(α)
main.b = shared(α)
α.x = owned(β)
α.y = uninitialized()
```
````

{anchor}`meta.syntax.heap.nodes`
Nodes can be frames, objects, primitives, or arrays. Owned, showned, and shlease references target objects, primitives, or arrays;
they cannot target frames. Unique leases target an owned or leased edge,
written `lease(α.f)`, `lease(main.p)`, or `lease(items[0])`. Declare each node and slot only
once. Forward references are permitted. Unicode identifiers work; optional quoted
labels use JSON string escaping. Blank lines and lines beginning with `#` are
ignored. Arguments are comma-separated; quoted arguments can contain commas.

{anchor}`meta.syntax.heap.constructors`
The supported constructors and assignments are:

- `frame()` uses its identifier as the label; `frame("name")` overrides it.
- `object(Point)` or `object(Point, "α")` declares a labeled aggregate.
- `primitive(22)` or `primitive(22, "β")` declares an opaque primitive label.
- `array(2)` or `array(2, "items")` declares a fixed number of slots.
- `main.p = owned(α)` sets a named slot; `items[0] = owned(β)` sets an array slot.
- Reference constructors are `owned`, `lease`, `showned`, and `shlease`.
  `leased` is an alias for `lease`; both require an edge target.
  `shared` is an alias for `shlease`, never inferred to mean `showned`.
- `uninitialized()` explicitly marks an empty slot. All array slots start empty.

{anchor}`meta.syntax.heap.validation`
The renderer rejects unknown targets, duplicate assignments, invalid projections,
and out-of-bounds indices. Lease targets must name an initialized owned or
leased edge; forward references to edges are permitted. Arrays in diagrams are limited to 64 slots for readable
output; that is a tooling limit, not a semantic array bound. The renderer accepts
ownership cycles and conflicting owners so that we can illustrate malformed
states. Structural validation is **not** validation of heap invariants.

{anchor}`meta.syntax.heap.rendering`
SVG diagrams preserve individual labeled references, with frames grouped on the
left when reachable objects allow it. A Rendered/Facts selector switches each diagram independently between its SVG
and its source facts, with Rendered selected initially. The SVG description also
exposes the input. Layout is deterministic, but does not add support
edges or infer lease provenance. Explicit lease targets are rendered as
junctions on the named edge. See {anchor-ref}`meta.rendering.faithfulness`.

### Checking the authoring claims

The preprocessor tests exercise these claims with valid examples and rejection
cases. `tests/book.rs` covers roles, links, literal contexts, and fenced-block
integration; `src/grammar.rs` covers data definitions and comments;
`src/graph.rs` covers heap facts. These are supporting tests, not an automated
claim-coverage certification. A machine-readable evidence association system
remains future work.

{anchor}`meta.syntax.heap.routing`
Diagram edges use horizontal and vertical segments, ending in dots. Object-targeting edges enter along the left boundary;
lease edges join their explicitly named supporting edge. The router seeks short paths with few bends through
corridors around object and frame boxes, including gaps within a column.
It avoids box interiors; it does not guarantee that edge paths or labels never
overlap. Lease junctions still identify the explicitly named supporting place.

{anchor}`meta.syntax.lean.mathematical_containers`
Within supported compact declarations, applications of `List T` and `Array T`
render as an overbar over `T`, denoting a finite ordered sequence. Applications
of `FiniteMap K V` render as `K ⇀ V`. Arguments may be identifiers or balanced
parenthesized expressions; nested supported applications use the same notation.
This display abstraction does not assert that Lean's list and array types are
identical. Unrecognized expressions retain their source spelling, escaped for
HTML. The Lean view retains the original declarations.

{anchor}`meta.syntax.lean.alignment`
In the compact view, `:=` and alternative separators `|` share one column.
A constructor with more than one parenthesized field keeps its first field beside
the constructor and displays subsequent fields on separate lines, aligned with
the first field’s opening parenthesis. Constructors with
zero or one field remain on one line. Nested parentheses within a field type
do not introduce additional fields.
