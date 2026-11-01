# Dada and this model

Dada explores ownership through operations that give values, share ownership,
and borrow access. Its goal is a Java-like object model with Rust-like control
of storage and lifetimes: programmers describe objects and their relationships
without requiring every object to occupy its own allocation.

The book is organized into language layers:

1. [Given](../given-overview.md) begins with [operational semantics](../given.md)
   for unique ownership, followed by a draft [type system](../given-typing.md)
   that tracks initialized, empty, and unknown places with views and proposes
   progress and preservation statements.
2. [Shared](../shared-overview.md) adds [operational semantics](../shared.md)
   for shared ownership. Its [type-system chapter](../shared-typing.md) is coming.
3. [CFlow](../cflow.md) reserves the next part for control flow.

Each language has its own syntax, execution rules, examples, and invariants.
A correspondence theorem shows that the translation of a Given program has
exactly its original execution behavior in Shared. The checked operational
models cover construction and fresh-variable bindings. Given also contains a
draft unpacking extension used by the typing chapter; neither unpacking nor
typing has been formalized in Lean yet. The existing preservation proofs concern
heap well-formedness. Assignment, drop, primitives, function calls, and borrowing
remain outside these models.

Later chapters will add features to this foundation one layer at a time. The
[design goals](tenets.md) explain the choices the model is intended to support.

The prose and mathematics stand on their own. A **Lean** selector reveals the
associated formal definition, theorem, or example. Lean checks proofs; recorded
reviews compare their statements with the explanation. The
[contributor guide](../introduction.md) describes that process.
