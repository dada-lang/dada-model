# Heap model

The first semantic model is a **heap machine**, parameterized by primitive values
and independent of Dada syntax. A client creates objects and frames and requests
operations such as giving a field, sharing a reference, replacing an array
element, or dropping an owner. We can study sequences of those operations before
introducing an expression evaluator.

We begin with objects and references: what exists, how operations change it,
and when an access goes wrong. We will later explain how memory layouts realize
this account and how a type system anticipates execution.

## Reading order

[State](state.md) introduces the objects and references in our pictures.
[Operations](operations.md) describes their effects; [examples](examples.md)
follow particular sequences. [Properties](properties.md) identifies what we
want to establish about all sequences, and [ownership views](ownership-views.md)
explores diagrams derived from the machine state.

The examples are handwritten scenarios and all properties are candidates.
[Questions to settle](questions.md) records the choices still needed before
implementing the machine.

## Development phases

1. Define this object machine and execute heap operations, including arrays and
   uninitialized slots needed to discuss unsafe code.
2. Establish invariants and use them to construct explanatory ownership views.
3. Introduce Dada's type system and relate its restrictions to execution.

Word-level implementations and their correspondence to this machine are later
work. This first model does not yet describe user-defined destructors,
concurrency, or a complete unsafe-code interface.
