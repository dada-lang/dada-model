# Questions to settle

This chapter records unresolved choices so that the first Lean definitions do
not silently decide them. It is a design discussion, not current machine behavior.

## Reference representation

Unique leases target the unique edge from which they derive. How are supporting places
updated or invalidated across moves and replacement? What distinguishes
validity from being active? What information supports sublease promotion when
an intermediate lease is dead? Shared leases may need different information,
since they can survive transfer into shared ownership and loss of one owner.

How are invalid references represented? Possibilities include reference status,
object generations, or other invalidation metadata. We have not selected one.
Dead object identities must not accidentally become valid again through reuse.
Likewise, an old lease to a deallocated variable must not become valid again if a
later binding reuses its identity. The intended execution semantics α-renames each
binding lifetime to a fresh runtime identity. Its freshness supply and connection
to the heap rules remain to be formalized: heap allocation currently checks only
that the identity is absent from the live variable map.

## Access composition

Define the result of each give/share/lease/drop operation through each reference
kind, including nested field and array access. Resolve paths without bypassing
restrictions inherited from intermediate references. State permissions for array
length and observations of primitive payloads.

## Mutation and cleanup

Specify which borrows a mutation invalidates, including disjoint fields and
lease ancestors and descendants. Define replacement order, self-assignment and
overlapping source/destination cases. Decide how cleanup handles invalid leases,
uninitialized slots, cycles, and destruction order.

## Operation boundaries

The heap now has explicit variable allocation and deallocation. Allocation creates
an uninitialized slot; deallocation requires that the slot is uninitialized.
Specify how block exits and function returns order drops and deallocations,
including cleanup after faults. No live owner may exist outside the state
accounted for by the invariant. Decide whether faults are atomic, expose a
partially changed state, or terminate execution with a final diagnostic state.

## First implementation slice

Variable allocation and deallocation are the first formalized transitions.
Continue with primitive and aggregate creation, unique-owner transfer, sharing,
showned duplication, and release. Use the shared-ownership example to
refine validity. Add arrays and partial initialization before treating this as
an interface for unsafe Dada code. Introduce unique leasing and promotion with
explicit examples rather than guessing their transition rules.

This ordering is an implementation proposal. The vocabulary of the heap model
already includes all three object forms and all four reference kinds.
