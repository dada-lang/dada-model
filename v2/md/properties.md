# Invariants and proof obligations

Everything in this chapter is a **candidate claim**, not a completed proof.
We will refine its prose and formal proposition together as transitions become
precise. The shields identify claims and support cross-references. They do not imply
formalization, a completed review, or a checked proof.

## Ownership exclusivity

{anchor}`heap.ownership.exclusive`
Starting from an empty machine, no finite
sequence of successful operations creates two uniquely owning references to the
same object or mixes unique ownership with shared ownership of that object.

Let U(o) count owned references to object o, and S(o) count showned references.
For an allocated live object, the proposed ownership condition is:

```text
(U(o) = 1 and S(o) = 0) or (U(o) = 0 and S(o) >= 1)
```

Count initialized slots in **all** frames, objects, and arrays, including temporary
bindings. Counts concern reference occurrences in storage, not merely distinct
object targets. References retained solely as invalid diagnostic history must
not count as active owners.

An object with no owners is dead; two unique owners constitute malformed
ownership. Both fail the condition, but explain different failures.

The intended proof structure is induction over successful operations: the empty
state satisfies the invariant and each operation preserves it. The operation
interface must prevent clients from manufacturing owners or copying them
without a transition. The theorem does not apply to arbitrary hand-constructed
malformed states.

## Ownership transfer preserves contents

{anchor}`heap.give.preserves_object`
Giving a unique owner into a fresh
temporary preserves its target object and contents and transfers exactly one
ownership occurrence from source to destination. Existing shared leases are not
invalidated merely by that transfer.

This claim is scoped to unique-owner transfer. It does not settle giving through
all shared or leased access paths.

## Shared ownership preserves lifetime

{anchor}`heap.drop.nonfinal_showned`
Dropping a showned reference when another
showned reference to its target remains preserves the target and the validity
of its other references.

Proving only that the target remains allocated would not cover this entire claim:
the formalization must also account for reference validity and object contents.

{anchor}`heap.drop.final_owner`
Releasing the final owner destroys the target;
remaining references cannot subsequently be used to access it successfully.
Primitive destruction performs no recursive field releases. Aggregate and array
destruction release their initialized slots.

## Initialization and bounds

Uninitialized slots contribute no ownership, as specified by
{anchor-ref}`heap.slots.uninitialized`.

{anchor}`heap.slots.uninitialized_access`
Access requiring an uninitialized slot’s value faults, while initialization can fill it.

{anchor}`heap.array.bounds`
An array has exactly its length's worth of slots,
including uninitialized slots; indexing outside that range faults.

## Reference integrity

{anchor}`heap.references.valid_target`
Every valid reference in a reachable
state reaches a live object, directly or through a chain of unique lease targets. Diagnostic representations may retain invalid
references to destroyed objects, but those references cannot authorize access.

This needs a definition of validity. It cannot yet be proved from the minimal
state sketch, which intentionally leaves invalidation representation open.

## Further obligations

We should investigate locality of updates, frame cleanup, destruction termination,
and the rules for unique leases. These are not consequences of ownership counts
alone. In particular, one owner per object does not exclude an ownership cycle
unreachable from frames, and does not establish absence of leaks.

“No sequence creates duplicate unique ownership” is also weaker than saying
“no sequence goes wrong.” The machine intentionally describes operations that
can fault; a future type system will prevent some of those executions.
