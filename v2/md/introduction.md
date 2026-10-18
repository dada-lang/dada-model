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

Version 2 explores alternative ways to develop the semantics, beginning with an
abstract heap machine and combining prose, mathematical notation, Lean
formalization, and Rust-based book tooling. The
[older versions appendix](appendices/older-versions.md) describes the earlier
a-mir-formality-based model and links to its book.

At present, v2 is a design draft. The initial Lean formalization defines the
machine state, variable allocation and deallocation, and creation of primitive,
aggregate, and array objects, with checked lemmas about their local effects.
Creation fills an allocated, uninitialized destination with an owned reference
to a fresh object. Runtime variable identities are distinct from source names;
the future execution semantics will α-rename bindings to fresh identities and
manage their scopes. Most operations and proof obligations remain to be formalized.
Examples of the implemented operations cite checked Lean cases with explicit
resulting states. Longer proposed executions are marked as awaiting transition
rules and tests; the broader properties remain candidates.

The Rust book preprocessor renders mathematical notation, included Lean source,
anchor shields, cross-references, and fact-based heap diagrams. A successful
mdBook build checks rendering and citations, not the semantics or truth of the
content. The proposed heap behavior is not a claim that v1 already implements it
in every case.

## Where to begin

[How it works](repo/how-it-works.md) describes the development and reading process.
[Repository goals and principles](repo/tenets.md) explain our working principles, and
[Specification system design](repo/spec-system.md) states requirements for the
planned tooling.

[About Dada](dada/introduction.md) introduces the language's aims. The
[heap model](heap.md) begins the semantic definition with objects, references,
and operations, before introducing Dada's type system.
