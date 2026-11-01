# Contributing to the specification

This repository develops Dada's semantics as a book of definitions, execution
rules, examples, and theorems linked to Lean. Changes should keep the intended
behavior clear in the prose and precise in the formalization.

Agents help draft and review these accounts. Their correspondence reviews record
which inputs they examined, their conclusion, and the reason for it. Changed
inputs make those reviews stale. A review is evidence of a comparison, not a
substitute for proof checking.

## Contributor guides

- [Writing style tenets](repo/writing-style.md): explain intent through examples
  and introduce concepts in dependency order.
- [Authoring units](repo/authoring.md): write definitions and examples with named
  source citations.
- [Correspondence review](repo/correspondence-review.md): compare intent with
  formal statements and record reproducible evidence.
- [Extending the model in layers](repo/layer-extension.md): add a language feature
  and prove its relationship to the preceding layer.
- [How it works](repo/how-it-works.md) and [repository principles](repo/tenets.md):
  the development process and its goals.

The [specification system reference](repo/spec-system.md) defines the renderer
and evidence requirements. The [implementation contracts](repo/evidence-pilot.md) link tooling requirements
to code, tests, and review evidence. To read the language rather than work on
its specification, begin with [Dada and this model](dada/introduction.md).
