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
An operation that produces a reference places it in a destination binding in
`S′`. Fresh temporary frame bindings hold intermediate results, so all owning
references remain represented in the machine state.

{example} Giving from an access path into a temporary binding is written:

```text
S ──give(main, p.items[3], tmp)──▶ S′
```

Here `main` selects the frame, `p.items[3]` is the access path, and `tmp` names
the destination binding. The transition rules will determine the resulting state.

{informational} This judgment fixes the shape of successful steps. The rules for
individual operations are developed below and remain incomplete. We use a
relation rather than assuming a total `State → State` function: an operation
can fault, and allocation may choose a fresh identity. The representation of
faults and the state observable after a fault remain to be specified. Absence
of a rule in this draft is not by itself a definition of a fault.

## Frame creation

The first transition creates a frame whose requested binding names form the
sequence \\(\overline{x}\\). This is the currently defined operation grammar;
the operations discussed later in this chapter will extend it:

```{grammar} Heap:Operation
\omega ::= \mathsf{createFrame}(\overline{x})
```

Use the [state notation](state.md): \\(O\\) is the object map, \\(F\\) the
frame map, and \\(\iota\\) a frame identity. The rule names the new binding map
\\(B\\), new frame \\(b\\), and updated frame map \\(F^{\prime}\\).
\\(\operatorname{dom}(F)\\) is the set of keys in \\(F\\);
\\(F[\iota \mapsto b]\\) adds the fresh association \\(\iota \mapsto b\\)
and retains every existing association:

```{rule} Heap:Step.createFrame
\frac{
  \begin{gathered}
    \operatorname{distinct}(\overline{x}) \\
    \iota \notin \operatorname{dom}(F) \\
    B = [\, x \mapsto \bot \mid x \in \overline{x} \,] \\
    b = \mathsf{frame}(B) \\
    F' = F[\iota \mapsto b]
  \end{gathered}
}{
  \langle O, F \rangle
  \xrightarrow{\mathsf{createFrame}(\overline{x})}
  \langle O, F' \rangle
}
\;\text{CreateFrame}
```

The premise \\(\operatorname{distinct}(\overline{x})\\) requires each requested
name to occur once. The comprehension defining \\(B\\) gives every requested
binding an uninitialized slot; it introduces no other bindings. Freshness of
\\(\iota\\) ensures that the new frame replaces no existing frame.

{informational} The Lean selector provides the cited rule for hand comparison.
Its `names`, `id`, `bindings`, `frame`, and `frames'` correspond to
\\(\overline{x},\iota,B,b,F^{\prime}\\). Its helpers `initialBindings` and `insertFresh`
implement the displayed map construction and fresh extension. These helpers
retain the requested binding order and prepend the fresh frame association in
their list representation. The mathematical view omits proof terms while
retaining the distinctness, freshness, and defining-equation premises.
Correspondence between the views remains a review obligation.

{anchor}`heap.create_frame.fresh`
Creating a frame chooses an ID absent from the current frame map and adds a new
frame under that ID. Existing frames remain unchanged.

{anchor}`heap.create_frame.bindings`
The requested binding names must be distinct. The new frame has exactly those
bindings, each containing an uninitialized slot.

{anchor}`heap.create_frame.objects_unchanged`
Creating a frame leaves the object map unchanged.

{informational} `Step` is a successful-transition relation. Its `createFrame`
constructor carries the chosen ID and proofs of the freshness and distinctness
conditions. The operation label supplies the binding names; the successor state
contains the new frame. This first rule does not choose a policy for faults or
identity reuse after frame destruction. Frame destruction is not yet modeled.

The declarations and proofs live in `lean/Heap.lean`. Lean checks
`createFrame_preserves_objects` for the object-map claim and
`initialBindings_are_uninitialized` for the uninitialized-content part of the
binding claim. These proofs do not establish the later ownership invariants.

## Creation

Creating a primitive object stores a supplied value \\(v \in P\\). Creating an
aggregate supplies its field names; creating an array supplies its length.
Aggregate and array slots begin uninitialized. Each creation produces one owned
reference to a fresh object in a destination binding.

Creating a frame establishes its bindings as uninitialized. Freshness prevents
an allocation from accidentally reusing the identity of a live object.

## Give, share, lease, and drop

Field access must say which operation is requested:

```text
give(frame, access_path, destination)
share(frame, access_path, destination)
lease(frame, access_path, destination)
drop(frame, access_path)
```

The destination denotes a fresh temporary binding in this provisional notation.
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

Other fault cases include a missing binding or field and a projection inappropriate
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
cascade through owning fields. Frame destruction similarly releases its bindings.
Destruction order, cycles, and invalid borrowed references encountered during
cleanup require explicit decisions before defining a total algorithm.
