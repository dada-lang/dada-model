# Invariants and proof obligations

The [state chapter](state.md#well-formed-states) defines well-formedness:
every allocated object has an owning path from a variable, every stored reference
resolves to a live object, and each unique owner is the sole owner of its
target. Here we distinguish properties
preserved by the current operations from obligations requiring further rules.
We use its [reachability definition](state.md#well-formedness-and-reachability)
to relate a property of a state to complete executions.

## Ownership accounting

The ownership proofs track reference occurrences across all variable slots,
aggregate fields, and array elements. They use the following accounting
invariant, which follows from {anchor-ref}`heap.state.well_formed` but is weaker
than full well-formedness.

```{definition} Invariants:OwnershipInvariant
{anchor}`heap.ownership.exclusive`
Write \\(\mathsf{Own}(S)\\) for the following ownership conditions:

1. Every owning reference targets an allocated object.
2. Every allocated object has at least one owner.
3. Two unique owners of the same object must occupy the same place.
4. Unique and shared ownership cannot coexist for the same object.

\\[
\begin{aligned}
\mathsf{Own}(S) \iff{}& \\
 &\forall p,\alpha.\;\mathsf{owner}_S(p,\alpha)
       \Rightarrow \alpha\in\operatorname{dom}(O) \\
{}\land{}&\forall\alpha\in\operatorname{dom}(O).\;
       \exists p.\;\mathsf{owner}_S(p,\alpha) \\
{}\land{}&\forall p,q,\alpha.\;
       S(p)=\mathsf{owned}(\alpha) \land S(q)=\mathsf{owned}(\alpha)
       \Rightarrow p=q \\
{}\land{}&\forall p,q,\alpha.\;
       S(p)=\mathsf{owned}(\alpha)
       \Rightarrow S(q)\ne\mathsf{showned}(\alpha)
\end{aligned}
\\]
```

Here \\(S(q)\ne r\\) means that \\(q\\) does not store that reference,
including when the slot is absent or uninitialized. Leases are not owners;
these conditions do not limit their number or establish which lease is active.

### Initial state

```{theorem} WellFormed:initial_wellFormed
The empty state is well-formed.

\\[
\mathsf{WF}(\langle\varnothing,\epsilon\rangle)
\\]

**Proof outline.** There are no objects requiring owners and no stored
references requiring targets, support slots, or exclusivity checks. The allocated,
owning-path-reachable, and reference-reachable object sets are all empty.
```

### Preservation by allocation and creation

```{theorem} Invariants:step_preserves_ownership
Allocation and creation preserve ownership.

\\[
\frac{
  \begin{gathered}
    \mathsf{Own}(S) \\
    S \xrightarrow{\omega}_{\mathsf{alloc/create}} S'
  \end{gathered}
}{\mathsf{Own}(S')}
\\]

**Proof outline.** Pushing or popping an empty variable changes no reference
occurrences. Creation adds one fresh object and its sole owner in an empty
destination. Its initially empty contents add no further references, and every
existing object's owners are preserved.
```

This theorem covers every current constructor of `Heap.Step`: pushing an empty
variable, popping an empty top variable, and creating a primitive, aggregate,
or array in an empty destination. It accepts any input satisfying the invariant;
it does not assume the desired invariant as a transition precondition on the
output. Creation adds exactly one object and one owner. New aggregate fields and
array elements contribute no references.

### Reachable states

```{theorem} PathOperations:machineReachable_preserves_ownership
Every state reached by finitely many machine steps from the initial state
satisfies the ownership invariant.

\\[
\frac{
  \langle\varnothing,\epsilon\rangle
    \xrightarrow{*} S
}{\mathsf{Own}(S)}
\\]

**Proof outline.** Induct on the execution. The empty execution uses the
initial-state result. Each additional step preserves the invariant established
for the preceding state.
```

`MachineReachable` is the finite closure of `MachineStep` from the initial state.
It includes the path operations and the allocation/creation slice. This result
does not imply that every stored borrow remains usable: ownership and borrow
validity are different properties.

```{theorem} PathOperations:MachineStep.preserves_ownership
A machine step preserves ownership whenever its input satisfies the invariant.

\\[
\frac{\mathsf{Own}(S)\qquad S\xrightarrow{\omega}S'}{\mathsf{Own}(S')}
\\]

**Proof outline.** Each machine step is either an allocation/creation step or a
path operation. Apply the corresponding preservation result to the input state.
```

```{example} Invariants:creation_preserves_ownership
Allocate `x` in the empty heap, then create primitive `22` in it. Both states are
reachable by the checked rules, and the resulting state satisfies the ownership
invariant.
```

```{example} Invariants:duplicate_unique_owners
A state with variables `x` and `y` both holding an owned reference to the same
primitive object violates the invariant. The Lean case proves that no witness
of `OwnershipInvariant` can exist for this state.
```

### Place operations and cleanup effects

The [place-operation chapter](place-operations.md#ownership-preservation) proves
ownership preservation for path-based reference transfer, borrowing, and
shared-owner duplication and release. Consuming moves retarget dependent unique
leases. Separate cleanup effects prove preservation when releasing reference
storage, including recursive destruction. Static access restrictions and
dynamic borrow invalidation remain outside these ownership proofs.

Ownership accounting does not establish acyclicity or reachability from variables.
A disconnected cycle can satisfy these equations, but fails well-formedness:
its objects have no owning path from a variable. Nor does ownership accounting
establish that a borrow is valid, active, or usable for mutation. Those require
additional predicates and proofs, listed below.

## Ownership transfer preserves contents

{obligation}`heap.give.preserves_object`
The consuming move transfers the selected reference and changes its former slot
to uninitialized. Its direct dependent leases follow the reference to the new
slot; deeper descendants keep their intermediate supports. Object identities,
primitive payloads, and shared-lease targets are unchanged. Stored unique leases
inside objects may change support, so the entire object map need not be equal
before and after the move. See the [move rules](place-operations.md).

Any stronger claim that the target's complete contents are unchanged must account
for those support updates and require the source to lie outside its target
object. Ownership accounting alone does not establish that: a self-owning object
is an ownership cycle. Giving through shared or leased paths can copy or reborrow
rather than consume the reference; the path rules distinguish these cases.

## Shared ownership preserves lifetime

{obligation}`heap.drop.nonfinal_showned`
Releasing a stored showned reference when another
showned reference to its target remains preserves the target and the validity
of its other references.

The checked resource effect clears only the selected showned occurrence and keeps
the object allocated. It leaves reference representations elsewhere unchanged.
Proving only that the target remains allocated does not cover the validity claim:
the formalization must also account for reference validity and object contents.

{obligation}`heap.drop.final_owner`
Releasing the final owner destroys the target;
remaining references cannot subsequently be used to access it successfully.
The checked resource-effect rules remove primitives directly and recursively
release initialized aggregate fields and array elements before removing their
container. They preserve ownership; reference invalidation and non-revival after
identity reuse are still required to prove the full claim.

## Initialization and bounds

Uninitialized slots contribute no ownership, as specified by
{anchor-ref}`heap.slots.uninitialized`.

{obligation}`heap.slots.uninitialized_access`
Access requiring an uninitialized slot’s value faults, while initialization can fill it.

{obligation}`heap.array.bounds`
An array has exactly its length's worth of slots,
including uninitialized slots; indexing outside that range faults.

## Reference integrity

The slot condition of {anchor-ref}`heap.state.well_formed` requires each existing
slot to be uninitialized or to contain a reference that resolves to a live object.
Unique leases therefore need finite, initialized support chains. This condition
checks every stored reference, including one whose failed traversal would
contribute nothing to a set of reachable objects. Ownership counts alone do not
establish it.

```{theorem} WellFormed:MoveReference.preserves_wellFormed
A consuming reference move into a variable preserves well-formedness. Write
\\(S\xrightarrow{p\rightsquigarrow x}_{\mathsf{move}}S'\\) for moving a stored
reference from \\(p\\) into an allocated, empty variable \\(x\\), including the
retargeting of dependent leases.

\\[
\frac{\mathsf{WF}(S)\qquad S\xrightarrow{p\rightsquigarrow x}_{\mathsf{move}}S'}{
 \mathsf{WF}(S')}
\\]

**Proof outline.** The move preserves ownership. An owning path that used the
source reference can instead begin at the destination variable, so every
allocated object retains an owning path from a variable. Every reference in the result
comes from a reference in the input, either unchanged or with its supporting
place retargeted. Transport its finite resolution along the move to obtain a
resolution to the same live object in the result.
```

The variable destination matters. Moving an owner into a field of its own object
could leave an ownership cycle with no path from a variable. General transfers
into fields or array elements need conditions that preserve rooted liveness.

### The remaining drop obligation

```{example} WellFormed:reachable_drop_leaves_dangling
Choose natural-number primitives and start from the empty state:

1. Allocate variable \\(x\\), then a distinct variable \\(y\\).
2. Create a primitive holding `22` into \\(x\\), making it the unique owner.
3. Share \\(x\\) into \\(y\\), which now holds a shared lease to the object.
4. Drop through \\(x\\).

Before the drop, the state is well-formed. The current drop rule removes the
object and clears \\(x\\), but leaves the shared lease in \\(y\\). The successor
still satisfies ownership, since there are no objects or owners left. It fails
the well-formedness slot condition because the remaining shared lease targets
the deleted object.

The Lean test proves reachability of both states, well-formedness before the
drop, and failure of reference resolution afterward. No identity reuse is involved.
```

{obligation}`heap.references.valid_target`
The machine's completed reference-lifetime rules should preserve well-formedness
across permitted executions. The current drop rules do not preserve the slot
condition. We must constrain destruction when borrows survive, or
represent invalidation explicitly and revise well-formedness to distinguish
invalid handles from usable references. That choice remains open.

This obligation cannot be discharged just by reusing the ownership preservation
proof: the checked example exhibits a well-formed input with a non-well-formed
successor. Nor does finite resolution establish whether a lease is active or
whether concurrent access is permitted.

## Further obligations

We should investigate locality of updates, scope cleanup, destruction termination,
and the rules for unique leases. These are not consequences of ownership counts
alone. In particular, one owner per object does not exclude an ownership cycle
unreachable from variables. Well-formedness excludes those disconnected objects;
preserving it requires more than preserving ownership counts. Rooted liveness
also does not by itself establish termination of recursive destruction or eventual
release of every object.

The heap's allocation rule checks absence from the current variable store.
The execution semantics must satisfy the
[binding-lifetime obligation](operations.md#scope-and-binding-lifetimes): a new
allocation must not revive a lease to a retired binding. Deallocation removes only
the newest live slot, and only when it is uninitialized. Proving that scope
cleanup releases each slot's contents before popping it requires the
complete scope and invalidation rules above the checked release effects. Current
path-drop through borrowed access leaves the state unchanged; cleanup of the
stored borrowed reference is a separate effect.

Object creation likewise chooses an identity absent from the current object map.
The path-drop rules can destroy objects. The current rules do not retain retired
identities, so they do not yet prevent identity reuse from reviving old
references. Constraining destruction to preserve the slot condition, tracking freshness,
or explicitly invalidating references are possible approaches. Reference
integrity is not a consequence of ownership preservation.

“No sequence creates duplicate unique ownership” is also weaker than saying
“no sequence goes wrong.” The machine intentionally describes operations that
can fault; a future type system will prevent some of those executions.
