# Operations on the machine

{anchor}`heap.steps.judgment`
Successful execution of a heap operation is a transition between machine states:

```{judgment} Heap:Step
\begin{gathered}
S,S' \in \mathsf{State} \qquad \omega \in \mathsf{Operation} \\
S \xrightarrow{\omega} S'
\end{gathered}
```

The judgment reads: performing \\(\omega\\) in state \\(S\\) can take one
machine step to state \\(S^{\prime}\\). The operation label includes its explicit
arguments. For each fixed \\(\omega\\), this is a relation on pairs of states;
there is no separate returned value outside the successor state.

{anchor}`heap.steps.results_in_state`
An operation that produces a reference places it in an allocated destination
variable in `S′`. Temporary variables hold intermediate results, so all owning
references remain represented in the machine state. Allocate a temporary slot
before using it as a destination.

{example} Giving from an access path into a temporary variable is written:

```text
S ──give(p.items[3], tmp)──▶ S′
```

Here `p.items[3]` is the access path, and `tmp` identifies the allocated
destination variable. The transition rules will determine the resulting state.

{informational} This judgment fixes the shape of successful steps. The rules for
individual operations are developed below and remain incomplete. We use a
relation rather than assuming a total `State → State` function: operations may
fault. The representation of faults and the state observable after a fault
remain to be specified. Absence
of a rule in this draft is not by itself a definition of a fault.

## Variable allocation and deallocation

The initial machine state has empty object and variable maps. Variables are
introduced individually, so entering a block does not require knowing all of
its slots in advance. The currently defined operation grammar is:

```{grammar} Heap:Operation
\omega ::= \mathsf{allocVariable}(x) \mid \mathsf{deallocVariable}(x)
```

Use the [state notation](state.md): \\(O\\) is the object map, \\(V\\) the
variable store, and \\(x\\) a runtime variable identity.
\\(\operatorname{dom}(V)\\) is the set of allocated variable identities.
\\(V[x \mapsto \bot]\\) extends the store with a fresh uninitialized slot;
\\(V \setminus x\\) removes the association for \\(x\\). Both operations retain
every other association.

```{rule} Heap:Step.allocVariable
\frac{
  \begin{gathered}
    x \notin \operatorname{dom}(V) \\
    V' = V[x \mapsto \bot]
  \end{gathered}
}{
  \langle O,V \rangle
  \xrightarrow{\mathsf{allocVariable}(x)}
  \langle O,V' \rangle
}
\;\text{AllocVariable}
```

{anchor}`heap.variables.allocate`
Allocating a variable requires that its identity is absent from the variable
store. Allocation adds exactly that slot, initially uninitialized; it does not
overwrite an existing slot or change the object map.

The operation supplies the identity; the successful-step rule checks its
availability. The execution layer is also responsible for the stronger
{anchor-ref}`heap.variables.lifetimes` requirement: distinct allocation lifetimes
receive distinct identities. Absence from the current store alone does not prove
that an identity has never been used.

```{rule} Heap:Step.deallocVariable
\frac{
  \begin{gathered}
    V(x) = \bot \\
    V' = V \setminus x
  \end{gathered}
}{
  \langle O,V \rangle
  \xrightarrow{\mathsf{deallocVariable}(x)}
  \langle O,V' \rangle
}
\;\text{DeallocVariable}
```

{anchor}`heap.variables.deallocate`
Deallocating a variable requires an allocated, uninitialized slot. It removes
that slot and preserves all other variables and objects. An absent slot is not
an uninitialized slot: it cannot be deallocated.

{anchor}`heap.variables.release_before_deallocation`
Deallocation does not release a reference implicitly. If a variable still
contains a reference when its scope ends, that reference must first be released
and the slot made uninitialized. Dropping a variable's contents and removing its
slot are separate operations.

{example} An inner scope can allocate \\(y\\), use it, release any remaining
contents, and deallocate \\(y\\), while an outer variable \\(x\\) stays allocated.
Both slots contribute to ownership accounting while they exist. The heap map
does not itself require last-in-first-out deallocation; the execution layer
chooses scope cleanup order.

{informational} The Lean selector provides each rule for hand comparison.
Its `objects`, `variables`, and `id` correspond to \\(O,V,x\\).
`insertFresh` implements fresh extension and `erase` implements removal.
The premise \\(V(x)=\bot\\) means the association \\((x,\bot)\\) occurs in the
finite map. The mathematical view omits proof terms but retains their conditions.
Correspondence between the views remains a review obligation.

The declarations and proofs live in `lean/Heap.lean`. The
`allocVariable_contents` and `deallocVariable_contents` lemmas characterize the
resulting variable maps exactly. The corresponding `*_preserves_objects` lemmas
prove that the object map is unchanged; `deallocVariable_rejects_initialized`
and `deallocVariable_rejects_absent` distinguish an empty slot from an initialized
or missing one.
These proofs do not establish global freshness across executions, call or scope
semantics, or the later ownership invariants.

{informational} Reference release and lease invalidation are still under design.
The only successful transitions formalized so far are allocation and
deallocation of variable slots. The prose about other operations below guides
future rules; it is not an implementation of `drop` or function calls.

## Creation

Creating a primitive object stores a supplied value \\(v \in P\\). Creating an
aggregate supplies its field names; creating an array supplies its length.
Aggregate and array slots begin uninitialized. Each creation produces one owned
reference to a fresh object in an allocated, uninitialized destination variable.
Freshness prevents object allocation from accidentally reusing the identity of a
live object.

## Give, share, lease, and drop

Field access must say which operation is requested:

```text
give(access_path, destination)
share(access_path, destination)
lease(access_path, destination)
drop(access_path)
```

The destination denotes an allocated, uninitialized variable in this provisional
notation; allocate a fresh temporary when an intermediate result needs one.
These are machine operations, not Dada source syntax.

The operation and the access route jointly determine the result. We cannot
implement every access by returning the reference stored in the final slot:
reaching an owned field through a shared reference must respect the shared access.
A generic operation called “read” would hide this choice.

The following commitments guide the transition definitions:

- Giving unique ownership transfers it without duplicating it. It does not
  intrinsically invalidate shared leases of the surviving object.
- Sharing an owned reference creates a shared lease while retaining ownership.
- Sharing a showned reference produces another showned reference.
- Leasing introduces unique borrowed access, not another owner.
- Dropping releases a reference and may trigger destruction.

The complete table for all reference kinds and composed access routes is still
open. In particular, giving through a shared route must not be assumed to
transfer the stored unique owner. “Giving always empties the selected slot” is
not an established rule for every access.

## Independent sharing

Turning a value into shared ownership is a separate operation from sharing a
place. In our examples, an owned value is first given into a temporary, then
converted to showned ownership. The conversion replaces its unique ownership;
it does not leave an owned reference alongside showned references.

The proposed result preserves the object and existing shleases. The transition
must account for the intermediate owner and any existing unique leases. The
latter case remains open; our first example has no unique leases.

## Initialization and assignment

Initialization fills an uninitialized slot. Assignment replaces initialized
contents as well. In both cases, an incoming owned reference must be consumed
from its source rather than copied. Replacing previous contents releases their
reference and may destroy their object.

A field assignment replaces the slot's reference; it is distinct from modifying
the primitive payload of the object formerly reached by that reference. A
primitive-payload update operation, if needed, has not yet been specified.

Mutation can invalidate borrowed references while leaving the referenced object alive.
We still need to define which references a particular mutation invalidates,
including the treatment of disjoint fields and unique lease descendants.

## Length and faults

Array length observes the number of slots without accessing element contents.
The required permission for that observation remains to be specified. Indexing
out of bounds faults. An operation requiring a value faults on an uninitialized
slot, and using an invalid reference faults. Initializing an empty slot is valid;
it does not require reading its previous contents.

Other fault cases include a missing variable or field and a projection inappropriate
for the target object. A full fault taxonomy will accompany the transitions.

## Reference release and object destruction

Dropping a leased or shlease reference does not itself destroy the referenced object.
Dropping a nonfinal showned reference leaves the object alive and preserves the
validity of its other references. Dropping the last owner destroys the object
and invalidates remaining references to it.

Destruction depends on the object's form:

- A primitive has no recursive destruction work.
- An aggregate releases each initialized field reference.
- An array releases each initialized element reference.

Uninitialized slots require no recursive release. Destruction can therefore
cascade through owning fields. Scope cleanup releases variable contents before
deallocating their slots. Destruction order, cycles, and invalid borrowed
references encountered during cleanup require explicit decisions before
defining a total algorithm.
