# Authoring units

A specification unit is one explanation that can be compared with a named formalization. Keep
its definition, qualifications, notation, and explanatory text inside the same
fence. The reader should understand the mathematical account without opening
Lean; the Lean view makes the associated formalization inspectable.

Use the [Writing style tenets](writing-style.md) to organize the explanation:
start with intent, use examples to make distinctions concrete, and introduce
notation before relying on it.

## Identity, formalization, and context

The opening argument is the unit ID. Source citations and dependencies are
options, followed by a blank line and the body:

````text
```{definition} unique.syntax.place
:lean: Unique/Syntax:Place
:uses: unique.syntax.variable unique.syntax.field

A *place expression* \\(p\\) identifies a variable or a field reached through another place.

\\[
p ::= x \mid p.f
\\]
```
````

This is an authoring illustration; it does not assert that these example modules
already exist. `unique.syntax.place` is the public unit identity.
`Unique/Syntax:Place` is a source selector relative to the configured Lean root.
They serve different purposes and need not have matching names.

A citation can select an inductive member of a top-level `mutual` group. The
group delimiters and member headers must start at column zero; each header ends
with `where` on its first line, and its body is indented. The Lean view shows the
selected declaration; the evidence packet retains its enclosing source. Nested
groups and mutual definitions of other kinds are unsupported.

Use `:uses:` for definitions and notation needed to interpret a unit. Link new
terminology to the unit that introduces it with `{anchor-ref}`. A visible link
supports the reader; an explicit dependency also records context that is used
without being quoted. The inventory includes unit references in the review
dependency set. Keep dependencies specific enough that a reviewer can explain
why each is needed.

Unit IDs share the book's global namespace. They use ASCII letters, digits,
dots, underscores, and hyphens and begin with a letter or digit. Keep an ID stable
when moving a unit between chapters. A second identifying `{anchor}` inside a
structured unit is unnecessary.

## Choosing a kind

| Kind | Body | Formalization |
| --- | --- | --- |
| `definition` | Markdown introducing a concept, including delimited math | One or more Lean definitions or a Rust implementation citation for a meta requirement |
| `grammar` | Raw display LaTeX | One or more Lean type declarations |
| `judgment` | Raw display LaTeX | One inductive declaration |
| `rule` | Raw display LaTeX | One inductive constructor |
| `theorem` | Markdown stating a result and its assumptions | One named Lean theorem |
| `lemma` | Markdown stating a supporting result and its assumptions | One named Lean theorem |
| `example` | Markdown explaining a concrete case | One anchored anonymous Lean example |
| `future-note` | Markdown exploring a possible future design, outside the current specification | Forbidden |

Theorem and lemma reviews compare the intended proposition with Lean's
statement, including hidden parameters and assumptions. Leave the proof to
Lean. A prose proof outline is not required. Definitions introduce concepts and
judgments; they do not require proofs.

Kind and readiness are separate. During a Markdown-first review, add
`:status: draft` to retain the intended kind with a separate **Draft** indicator:

````text
```{definition} unique.evaluation
:status: draft
:uses: unique.syntax.place

The following rules define expression evaluation.
```
````

A draft may omit source citations. Any supplied citations must still select the
right declaration kind. A draft theorem states a proposed result, not an
established one; a draft example describes a scenario awaiting its formal case.
Evidence validation fails while a unit is draft, and no affirmative
correspondence decision can be recorded for it. Add the matching formalization
and remove `:status: draft` before preparing a correspondence review.

### Future notes

Use a **Future note** for exploratory ideas that are not part of the current
specification. Unlike a draft specification, a future note is publishable without
formalization:

````text
```{future-note} future.generic_views
:uses: given.typing.views

A future design could preserve partial views through constructors.
```
````

Future notes reject `:lean:`, `:rust:`, `:tests:`, and `:status: draft`.
Place future notes at chapter top level, outside lists and blockquotes.
They have stable IDs, Markdown bodies, and optional `:uses:` context; links and
dependencies must resolve as usual. Nested specification units and legacy
citation blocks are forbidden. The header says **Future note**, with no source
selector. Evidence status is `future note` / `not applicable`; preparation and
recording of correspondence reviews are rejected. Once an idea has an associated
formalization, change it to the appropriate specification kind and review it.
These checks reject declared source associations; they do not discover uncited
implementations elsewhere in the repository.

### Checking the formalization

Check Lean with `just test-lean`; its `lake build --wfail` rejects warnings,
including those emitted by `sorry`. Do not use `sorry` to complete a formalization
or suppress `warn.sorry`.
Any future allowance for admissions must require an explicit opt-in.

Examples carry explanatory content too: describe the setup, the action, and the
result that the cited Lean case actually states. A test of one small helper does
not support an example claiming an entire execution. Use multiple units when
different cases need independent explanation and review.

## Mathematics and examples

Within Markdown bodies, use doubled-backslash delimiters: `\\(` and `\\)` for
inline mathematics, `\\[` and `\\]` for displays. Grammar, judgment, and rule
bodies are already LaTeX displays and do not need those delimiters. Put distinct
premises on separate lines. Group overbar expressions as `{\overline f}`; punctuation belongs outside the group.

Write source-language give expressions with the Unicode arrow, `p→`, and shared
conversion as `p→share`. Introduce a concept with its italicized name and inline
metavariable: “a *statement* \\(t\\)” or “a *value expression* \\(e\\).”
Give each metavariable a grammar or domain before using it; state map domains
and codomains explicitly. Define a judgment's notation and inference rules
before stating results about it. Use `:uses:` to identify earlier units that
supply these definitions. This is a correspondence-review requirement, not an
automatic notation check.

Abbreviating Lean syntax is useful when the omitted detail is explained;
omitting a condition such as freshness or distinctness changes the claim.

An example citation uses the name between standalone Lean anchor comments:

````text
```{example} unique.example.move
:lean: Unique/Examples:move
:uses: unique.operation.give

The example starts with one owner in `x`. Evaluating `x→` transfers that
reference and leaves `x` uninitialized.
```
````

The corresponding Lean region has exactly one anonymous `example`:

```lean
-- ANCHOR: move
example : True := by
  trivial
-- ANCHOR_END: move
```

This deliberately trivial snippet illustrates anchor syntax only. It does not
check the move described above and would not pass a correspondence review of
that example. Actual cases must state the relevant setup and result.

Use a longer outer fence for bodies containing fenced diagrams or code. Named
units are top-level review boundaries; do not nest them. A diagram inside an
example belongs to that example's reviewed body. Legacy citation directives
also cannot appear inside a structured unit: make them separate units with
`:lean:` citations and connect them with `:uses:`.

Write reviewed text directly in its unit. mdBook include, playground, and
rustdoc-include expansion is rejected in structured units, including inside
literal code samples: mdBook can expand those samples too. This keeps the
published claim equal to the text retained for review. To discuss an expansion
command literally, split its opening braces so it is not a live mdBook directive.

`book.toml` supplies the book source directory and `preprocessor.dada.lean-source`
for both rendering and evidence. It participates in review freshness. Source
roots must stay inside the project; changing a configured root requires a new
comparison with the declarations under that root.

## Requirements on the tooling

Meta requirements use the same unit identity and body structure. Cite Rust
implementation symbols and tests instead of a Lean formalization:

````text
```{definition} meta.example.required_inputs
:rust: mdbook-dada/src/evidence.rs:validate
:tests: mdbook-dada/tests/evidence.rs:rejects_missing_input

Validation reports an error when a review omits a required source input.
```
````

These paths and names illustrate the option layout; select actual symbols when
authoring a requirement. Its selector is Rendered/Rust; the Lean-backed forms use
Rendered/Lean. Do not mix `:lean:` and `:rust:` on one unit. Split a
requirement with independently reviewed implementations into separate units and
connect their context with `:uses:`. A test citation identifies coverage to
inspect; it does not assert that the test was executed or prove all cases.

## Scope and migration

Every new-style unit under `md/` participates in required evidence.
`spec.json` additionally lists chapters subject to strict whole-chapter coverage.
In those chapters, put semantic prose inside units and use headings for
navigation. The authoring illustrations and workflow explanations
in this repository section remain outside the initial strict pilot scope.

Existing chapters can retain the older opening-line citation syntax until they
are migrated. Their inline anchors and working Rendered/Lean selectors are
preserved, but do not by themselves provide complete review units. Migration
means choosing boundaries, moving explanations inside them, adding IDs and
dependencies, and preparing reviews. It is not a mass relabeling exercise.

After editing a covered unit, follow [Correspondence review](correspondence-review.md)
to prepare a fresh packet and retain the comparison evidence.

## Check definition links

Link each referenced concept or equation where it is used, including MathJax
rule premises. Ordinary Markdown links, anchor-reference roles, and MathJax
`\href{#claim-UNIT}{symbol}` are inventoried automatically. Cross-chapter
MathJax links use `.html` paths. Leave defining occurrences unlinked.

Run `dada-spec links` to inspect destinations and reading order. The
[link-review procedure](link-audits.md) explains coverage, target clarity, and
forward-reference evidence. A link that resolves is only the start: it should
land directly on the definition the reader needs.
