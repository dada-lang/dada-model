# Future tooling work

## Auditing links to definitions

```{future-note} future.tooling.link_audits
:uses: meta.syntax.anchors.identity meta.evidence.required_inputs

A reader should be able to follow a concept or equation to its definition
without searching within a larger block. Extend the
[writing conventions](writing-style.md#give-every-symbol-a-home) with link
audits for every definition, example, judgment, rule, theorem, and lemma.
Each audit should cover the entire block: natural-language text, inline
mathematics, and display mathematics.

The intended checks have two sides:

- **At each use:** every referenced concept, operation, judgment, or equation
  links to its definition. Check occurrences in prose and MathJax, including
  inference-rule premises. The defining occurrence itself needs no self-link;
  locally bound names must have an explicit introduction and scope.
- **At each destination:** the linked subject has a clearly identified
  definition or equation of its own. The anchor lands directly on that subject,
  rather than on a multi-part block in which the reader must find it. Review
  evidence should explain why the destination satisfies this requirement.

A possible implementation is an explicit inventory of references and defining
anchors, shared by prose and MathJax. A deterministic lint could check occurrence
coverage against that inventory, missing or ambiguous targets, and the presence
and freshness of the required review evidence, with source-located diagnostics.
The inventory format and treatment of locally introduced notation remain to be
designed.

Review must also check that the inventory is complete and that each destination
actually defines the intended subject clearly. Resolving an anchor alone cannot
establish either fact. Retain the source block, referenced definitions, relevant
surrounding text, inventory, audit policy, and relevant rendering inputs, together
with the conclusion and rationale. Check that links still land on the intended
subject in the rendered book. Changes to those inputs should invalidate the
affected evidence.

This is planned work. The current anchor checks and correspondence reviews do
not provide this complete link audit.
```

## Auditing conceptual order

```{future-note} future.tooling.reference_order
:uses: future.tooling.link_audits

Use the [link inventory](#claim-future.tooling.link_audits) to classify conceptual
references as backward, local, or forward. The intended reading order comes from
the book's table of contents and the position of each use and definition within
its chapter. The lint should detect uses before their definitions, including
within a single block, and identify cycles in conceptual dependencies.

Prefer rearranging the explanation to remove a forward reference. Each remaining
forward reference should require review evidence establishing all three points:

- **Necessary:** moving the definition earlier, moving the use later, or
  splitting a multi-part explanation cannot avoid the reference while preserving
  a coherent introduction. Record the alternatives considered and why they fail.
- **Explicit:** the text identifies the reference as forward and tells the
  reader where the concept will be defined.
- **Minimal:** the passage uses only the facts needed at that point, states
  those facts, and defers details that require the later definition. Identify
  exactly what the reader is being asked to assume.

The deterministic check should require a current justification for each forward
occurrence. Review judges its necessity, signposting, and limited use; the
existence of a link or a dependency cycle does not justify an exception by itself.
Distinguish conceptual dependencies from navigation-only links in the inventory,
and review that classification so it cannot hide an unexplained dependency.

Retain the source passage, target definition, relevant surrounding units,
dependency graph, and reading order as evidence inputs. Changes to the text,
definitions, or ordering should invalidate affected judgments. This extends the
planned link audit; it is not a check the current tooling performs.
```
