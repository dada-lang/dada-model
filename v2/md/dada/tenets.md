# Design goals and principles

These goals describe Dada's intended design. They are distinct from the
[repository's methods](../repo/tenets.md) for documenting and verifying it.
Their realization remains work for the specification and implementations.

## Java-like mental model, Rust-like execution

A programmer should be able to think in terms of objects and references without
first reconstructing stack offsets, inline storage, or reference-count headers.
An abstract object need not occupy a separate allocation. A concrete implementation
may place several abstract objects within one memory region.

Ownership remains meaningful in the abstract account. References differ in
whether they keep an object alive and in how they permit access. Abstracting
storage does not erase destruction or invalid access.

## Composability and semantic equivalence

Types should compose according to the operations they permit. If two type
expressions permit the same operations with the same observable semantics, our
goal is for them to describe the same type rather than expose incidental
representation choices.

Consider the Rust-shaped alternatives `&Option<str>`, `&Option<String>`,
`Option<&String>`, and `Option<&str>`. They illustrate different placements of
borrowing and different string representations. For the shared optional-string
interface we want to express, Dada's goal is to use one type:

```text
shared Option[String]
```

This is an illustration of the intended Dada equivalence, not a claim that these
are interchangeable Rust types or that every expression above is a valid Rust
type (`Option<str>` in particular is excluded by
[`Option<T>`](https://doc.rust-lang.org/core/option/enum.Option.html)'s sized type parameter). Rust's distinctions carry additional
representation and operational consequences. The Dada model needs to make
precise which observations and operations determine the proposed equivalence.

## Execution independently of static checking

The machine's operations should have meanings we can explain without consulting
the type checker. Checking predicts and restricts executions, and may reject
some dynamically safe executions. This is a **gradual-typing-compatible** goal:
we want a foundation on which dynamic enforcement and static guarantees can
coexist, without claiming that the current model already implements gradual typing.

Rust did not adopt this as its language design approach: Dada aims to give a
useful execution account for programs before static permission checking. We must
still define faults and access rules; independence does not mean every unchecked
program is valid.

For example, the proposed heap model permits an owner to be transferred without
intrinsically invalidating existing shared leases of the surviving object. A
checker or concrete implementation may impose further restrictions because of
relocation or because it cannot establish continued validity.

## Tracing-friendly execution

We want efficient backends for the JVM, WASM-GC, WASM, and native x86. The semantics
should accommodate tracing garbage collectors as well as implementations using
explicit ownership and lifetime management. Abstract object identity should not
force an allocation strategy that makes one of these backends unnecessarily costly.

Uninitialized slots are part of this design discussion. Native implementations
should not be forced to perform unnecessary initialization solely to mimic a
tracing backend's representation. Conversely, a tracing backend must maintain
its collector's requirements. The model must distinguish abstract initialization
state from the concrete contents a backend requires for safe tracing.

## Proofs over unsafe code

Where the type system cannot establish a necessary property, our goal is to cover
the gap with SMT-proven predicates. Low-level operations should have explicit
obligations that library code can discharge, rather than leave those obligations
as informal promises merely because an operation is unsafe.

This is a language goal, distinct from our choice to explore the semantic model
and its metatheory in Lean. The interface for those predicates and their connection
to the type system remain to be designed.

## Lexical capability safety

We want information and value flow to be readily amenable to static analysis,
with authority carried through explicit values and lexical scope. In the spirit
of WASM's explicit capability boundaries, code should not acquire authority from
implicit ambient channels.

This goal excludes global variables, thread-local storage, and other dynamically
scoped mechanisms for implicitly acquiring values or capabilities. Capabilities
needed by an operation should arrive through its explicit inputs or lexically
captured values. The semantics must eventually explain those boundaries and how
backends preserve them.
