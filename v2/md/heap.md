# Heap model

The **heap machine** is parameterized by primitive values
and independent of Dada syntax. A client allocates variable slots, creates
objects, and requests operations such as giving a field, sharing a reference, replacing an array
element, or dropping an owner. We can study sequences of those operations before
introducing an expression evaluator.

The heap retains all live variables, including temporaries and suspended callers'
variables. Source names, lexical visibility, and the α-renaming of bindings to
fresh runtime identities belong to the execution semantics that will use this
machine.

The model defines objects and references, their state transitions, and the
requirements for successful access. Memory layouts and a type system's relation
to execution are separate layers.

## Reading order

[Objects, references, and variables](state.md#setting-the-stage) sets out the
state's components, the empty initial configuration, and the assumptions about
reachable states. [Heap invariants](properties.md) states the ownership claims
and their checked preservation theorems. These establish the setting for the
transition chapters: [Operations](operations.md) defines variable allocation,
deallocation, and object creation; [place operations](place-operations.md)
defines giving, leasing, sharing, and dropping through access paths.
[Examples](examples.md) follow particular transition sequences, and
[ownership views](ownership-views.md) explains diagrams derived from the state.

The examples distinguish checked Lean cases for allocation, creation, and place
operations from proposed complete executions whose remaining transitions need
formalization. Active-borrow validity, invalidation, and broader safety
properties remain under design. [Questions to settle](questions.md) records the
missing definitions and semantic choices.

## Scope

The object machine includes arrays and uninitialized slots, ownership invariants,
and explanatory ownership views. Its connection to Dada's type system and to
word-level implementations remains to be specified. The model does not describe
user-defined destructors, concurrency, or a complete unsafe-code interface.
