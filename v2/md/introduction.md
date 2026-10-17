# About this repository

Dada is a programming language exploring permission-based ownership: how values
can be given, shared, and leased while supporting both an object-oriented mental
model and efficient execution. This repository develops a definition of Dada's
semantics: what its programs mean, how they execute, and what guarantees static
checking can provide.

We are building that definition as a **literate specification**. This book carries
the narrative and English claims. Definitions, executable models, examples,
formal propositions, and proofs provide complementary views of the design.
The aim is an account that people and agents can understand, question, and extend.

## An experimental, AI-assisted approach

We are experimenting with AI agents as collaborators in language design and
verification. Agents can help draft explanations, propose formalizations, explore
examples and counterexamples, implement operations, and review whether the pieces
express the same intent. Their work and review reasoning should be available for
inspection and revision.

Neither fluent prose nor an agent's approval establishes a mathematical result.
Likewise, proving a proposition does not establish that it captures everything we
intended. The process combines discussion, review, execution, and proof checking,
keeping their contributions distinct. Discrepancies are opportunities to improve
the design rather than occasions to automatically prefer one representation.

## Versions and current status

The original Rust model remains in `v1/` as an executable reference. Version 2
reimagines the specification, beginning with an abstract heap machine and planning
Lean definitions and proofs alongside Rust-based book and verification tooling.

At present, v2 is a design draft. Its examples are handwritten scenarios, its
properties are candidates, and no Lean implementation or checked proofs exist yet.
The Rust book preprocessor currently renders anchor shields, cross-references, and fact-based heap diagrams. A successful mdBook build checks rendering, not the
semantics or truth of the content. The proposed heap behavior is not a claim that
v1 already implements it in every case.

## Where to begin

[How it works](repo/how-it-works.md) describes the development and reading process.
[Repository goals and principles](repo/tenets.md) explain our working principles, and
[Specification system design](repo/spec-system.md) states requirements for the
planned tooling.

[About Dada](dada/introduction.md) introduces the language's aims. The
[heap model](heap.md) begins the semantic definition with objects, references,
and operations, before introducing Dada's type system.
