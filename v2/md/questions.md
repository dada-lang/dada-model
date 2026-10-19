# Questions to settle

This chapter records unresolved semantic choices. The questions identify gaps
in the machine's definition; they do not add transition rules.

## Reference representation

Unique leases target the unique edge from which they derive. Consuming moves
retarget every direct dependent lease to the destination; further descendants
keep their intermediate supporting places. Replacement and destruction still
need a policy for invalidation. What distinguishes validity from being active?
What information supports sublease promotion when
an intermediate lease is dead? Shared leases may need different information,
since they can survive transfer into shared ownership and loss of one owner.

The current rules have a checked counterexample to well-formedness preservation:
sharing a unique owner creates a shared lease, and dropping that owner can
leave the lease targeting a deleted object. See the
[drop obligation](properties.md#the-remaining-drop-obligation). Should the drop
be forbidden while that borrow survives, or should an invalid handle be
represented explicitly and excluded from usable references in well-formedness?

How are invalid references represented? Possibilities include reference status,
object generations, or other invalidation metadata. We have not selected one.
Dead object identities must not accidentally become valid again through reuse.
The current creation rules choose an identity absent from the allocated object map;
they do not track retired identities. The interaction between destruction,
subsequent identity reuse, and reference invalidation remains to be formalized.
Likewise, an old lease to a deallocated variable must not become valid again if a
later binding reuses its identity. The intended execution semantics α-renames each
binding lifetime to a fresh runtime identity. Its freshness supply and connection
to the heap rules remain to be formalized: heap allocation currently checks only
that the identity is absent from the live variable store.

## Access composition

The path resolver accumulates effective permission along the access route.
Owned inner edges retain a shared route's restrictions. Showned results require
a stored showned occurrence; an owned field under a showned parent needs an
ownership conversion or a sharing-closure invariant before it can be duplicated.
Define that conversion and its effects on existing borrows. Destructive showned
drop requires a writable route because it mutates the selected slot; destructive
access through a shared prefix remains unspecified. Also define permissions for
array length and primitive observations, and whether any operation copies
primitive payloads.

## Mutation and cleanup

The basic live-lien conflict table is separate from runtime transitions.
Deriving live liens from types, aliases, and field-local dependencies requires a
checker; the machine also needs a runtime invalidation policy.
Specify which borrows a mutation invalidates, including disjoint fields and
lease ancestors and descendants. Define replacement order, self-assignment and
overlapping source/destination cases. Decide how cleanup handles invalid leases,
uninitialized slots, cycles, and destruction order. Borrowed path-drop leaves
the state unchanged, while a borrowed-slot cleanup effect clears the handle.
Specify their relationship at scope exit and how cleanup respects surviving
dependencies and the restrictions of a shared access route.

## Operation boundaries

The heap has explicit variable allocation and deallocation with a stack
discipline. Allocation pushes an uninitialized slot; deallocation pops only the
newest live slot and requires it to be uninitialized. Specify how block exits
and function returns release contents and remove slots in reverse allocation
order, including cleanup after faults. No live owner may exist outside the state
accounted for by the invariant. Decide whether faults are atomic, expose a
partially changed state, or terminate execution with a final diagnostic state.

## Remaining operations

Variable allocation and deallocation and creation of all three object forms are
formalized. Creation requires an allocated, uninitialized destination; aggregate
fields must be distinct, and array lengths may be zero. `MachineStep` combines
this slice with the path-operation rules, and ownership preservation is proved
for all its constructors. The [place-operations chapter](place-operations.md)
includes exact-state tests and separates runtime steps from resource cleanup
and static live-lien checks. Field and array initialization operations remain to
be connected to the checked storage updates. The shared-ownership examples
require a definition of validity. Array observations and mutation must be
specified before this forms an interface for unsafe Dada code. Lease activity,
promotion, and invalidation need explicit examples and transition rules.

Well-formedness requires every allocated object to have an owning path from a
variable, following `owned` or `showned` references. Consuming transfer into a
variable preserves this property. When adding field and array initialization,
what restrictions preserve those owning paths? An arbitrary transfer can move
an object's owner into its own field, leaving an ownership cycle disconnected
from variables even though ownership counts remain consistent. State how each
new transition preserves rooted liveness as well as reference integrity.
