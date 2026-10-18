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

## Scope of the specification

This specification defines an abstract heap machine through prose,
mathematical notation, and Lean formalization, with Rust-based book tooling.
The [older versions appendix](appendices/older-versions.md) provides access to
other versions of the semantics.

The specification is a design draft. The Lean formalization defines the
machine state, variable allocation and deallocation, and creation of primitive,
aggregate, and array objects, with checked local-effect and ownership-preservation theorems. A separate
[place-operations chapter](place-operations.md) formalizes path-dependent give,
lease, share, and drop rules, with ownership proofs and exact-state examples.
Dependent leases follow consuming moves while retaining their target and
effective permission. Static live-lien restrictions are specified separately
from runtime path operations.
Creation fills an allocated, uninitialized destination with an owned reference
to a fresh object. Runtime variable identities are distinct from source names;
the future execution semantics will α-rename bindings to fresh identities and
manage their scopes. Assignment, ownership conversion, complete cleanup, and
borrow-validity obligations remain to be formalized.
Examples of the implemented operations cite checked Lean cases with explicit
resulting states. Longer proposed executions are marked as awaiting transition
rules and tests. Ownership preservation is proved for the stated relations;
reference validity, leak freedom, and termination remain open obligations.

The Rust book preprocessor renders mathematical notation, included Lean source,
anchor shields, cross-references, and fact-based heap diagrams. A successful
mdBook build checks rendering and citations, not the semantics or truth of the
content. Lean proof checking establishes the cited propositions; review checks
that those propositions express the accompanying mathematical claims.

## Where to begin

[How it works](repo/how-it-works.md) describes the development and reading process.
[Repository goals and principles](repo/tenets.md) explain our working principles, and
[Specification system design](repo/spec-system.md) states requirements for the
planned tooling.

[About Dada](dada/introduction.md) introduces the language's aims. The
[heap model](heap.md) begins the semantic definition with objects, references,
and operations, before introducing Dada's type system.
