# Extending the model in layers

Each semantic layer should be understandable on its own. Keep its syntax,
states, execution rules, examples, and invariants in distinct Lean modules
within the same Lake project. Shared proof infrastructure can be factored out
without making the earlier language depend on concepts introduced by a later
one. The book follows that same conceptual progression.

The opening chapters separate execution from static typing:

| Chapter | Scope |
| --- | --- |
| [Given: operational semantics](../given.md) | Classes, including empty classes; place and value expressions; `p→` transfers a unique owner. |
| [Given: typing and soundness](../given-typing.md) | Signed views track initialization and moves; progress, preservation, and completion are proved. |
| [Shared: operational semantics](../shared.md) | Extend execution with sharing of values, written `p→share`; traversal through shared ownership yields a shared copy. |
| [Shared: typing and soundness](../shared-typing.md) | Permissions determine whether giving moves or copies; views track accessible fields. Progress, preservation, and completion are proved. |

The two operational models live in `lean/Unique/` and `lean/Shared/`;
`lean/Correspondence/UniqueShared.lean`
proves the embedding preserves and reflects steps, finite executions, and
execution boundaries. Shared graph reasoning lives in `lean/Common/`.

Both layers support explicit `Class → { x, y }` unpacking patterns. Shared
requires a unique reference to the container; its fields may be shared.
The typing chapters define nominal types and signed views, expression and
statement typing, and the relation between typing environments and storage.
Given needs no permission types; Shared adds `given` and `shared`.

Progress says that a well-typed configuration is finished or can take a step.
Preservation says that every step retains configuration typing. Since each
step consumes one statement, well-typed programs also finish after exactly
one step per statement. These type soundness results are separate from the
structural heap invariants proved by the operational chapters.

Later extensions will cover control flow, class and struct distinctions,
primitives, destruction, and borrowing. Introduce each feature when its behavior
can be explained from the preceding chapters.

## Build one layer

Start with the behavior the layer adds and a small program that exhibits it.
Then introduce its objects and language, separating places from values, and
explain how evaluation changes a complete configuration.
Define liveness and well-formedness in terms of that layer's objects before
stating preservation theorems. Each definition and example belongs to a named
unit with Lean citations. Explanatory examples are part of the specification and
must state cases that can be checked in Lean.

For a theorem, first make the intended assumptions and conclusion clear in the
book and the Lean statement. Review that correspondence. Prove the statement
in Lean and check it mechanically. A difficult proof can reveal a mistaken rule
or an inadequate invariant, but difficulty alone is not a reason to weaken the
claim without discussion.

## Relate execution models

When a layer extends the operational semantics, it should faithfully contain
the earlier language. Define an
embedding of programs and configurations and a relation describing when a
configuration in each model represents the same execution state. The relation
must include enough information to discuss future steps, not just matching
object maps.

For a one-step correspondence, establish both directions:

- Every earlier-model step has a matching later-model step from the related
  configuration, and their results are related.
- Every later-model step from a related configuration has a matching
  earlier-model step, and their results are related.

The second direction rules out new behavior for translated earlier programs.
An equation mentioning only transitions whose endpoints are already embeddings
is insufficient: it can overlook a transition that leaves the embedded fragment.
State the theorem so that arbitrary successors in the later model are covered.

Also specify how initial configurations, final values, stuckness or faults, and
observable results correspond. If one model needs extra administrative steps,
choose and justify a relation allowing those steps instead of calling an
unproved one-step equivalence a bisimulation. Fresh identities may require a
renaming relation rather than literal state equality.

Keep this correspondence in a separate Lean module importing both layers. Its
proofs establish the relationship between the formal models. Review units
explain why that relationship captures the intended extension and cite the
translation and correspondence statements. Reviews do not replace the proofs.

## Record the extension's evidence

Review the new chapter's units with the same
[evidence procedure](correspondence-review.md). For typing, include the relevant
typing judgments, operational rules, and soundness statements. For an operational
extension, also review the correspondence units: include the relevant units from
both layers, their translation, and the formal correspondence statement as
inputs. Changing a source layer or the translation must invalidate affected
reviews, even if the prose of the correspondence theorem is unchanged.

Agent review has three distinct jobs: identify whether the units capture the
intended model, compare their prose and mathematics with Lean, and assess
whether the correspondence statement rules out unintended new behavior. Lean
checks the resulting proofs. The saved rationale makes each of those review
judgments open to a second review.
