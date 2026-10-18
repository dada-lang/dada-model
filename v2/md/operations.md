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

```{example} Heap:integer_primitive
Choose integer primitives. Allocate a temporary variable \\(x\\) in the empty
state. The resulting state \\(S\\) contains only this uninitialized slot. Creating
a primitive object holding `22` then takes this step:

\\[
S \xrightarrow{\mathsf{createPrimitive}(22,x)} S'
\\]

In \\(S'\\), \\(x\\) owns the new object \\(\alpha\\) holding `22`. The Lean view
calls the two states `allocated` and `created`, and proves both the allocation
and creation steps.
```

{informational} This judgment fixes the shape of successful steps. The rules for
individual operations are developed below and remain incomplete. We use a
relation rather than assuming a total `State → State` function: operations may
fault. The representation of faults and the state observable after a fault
remain to be specified. Absence of a rule in this draft is not by itself a
definition of a fault.

The currently defined operation grammar covers variable lifetimes and object
creation. Each creation operation requires an allocated, uninitialized destination
variable \\(x\\) and stores an owned reference to the new object there:

```{grammar} Heap:Operation
\begin{array}{rcl}
\omega &::=& \mathsf{allocVariable}(x) \\
       && \small\text{Push a new, uninitialized variable slot }x\text{.} \\[.6em]
       &\mid& \mathsf{deallocVariable}(x) \\
       && \small\text{Pop the newest, uninitialized slot }x\text{.} \\[.6em]
       &\mid& \mathsf{createPrimitive}(v,x) \\
       && \small\text{Create a primitive object holding }v\text{;} \\
       && \small\text{store its owned reference in }x\text{.} \\[.6em]
       &\mid& \mathsf{createAggregate}({\overline f},x) \\
       && \small\text{Create an aggregate with distinct fields }{\overline f}\text{,} \\
       && \small\text{all uninitialized; store its owned reference in }x\text{.} \\[.6em]
       &\mid& \mathsf{createArray}(n,x) \\
       && \small\text{Create an array of }n\text{ uninitialized slots;} \\
       && \small\text{store its owned reference in }x\text{.}
\end{array}
```

## Variable allocation and deallocation

The initial machine state has an empty object map and variable store. Variables are
introduced individually, so entering a block does not require knowing all of
its slots in advance.

Use the [state notation](state.md): \\(O\\) is the object map, \\(V\\) the
variable store, and \\(x\\) a runtime variable identity.
\\(\operatorname{dom}(V)\\) is the set of allocated variable identities.
\\((x:\bot)::V\\) pushes a fresh uninitialized slot onto the front of the
store. Allocation and deallocation obey
{anchor-ref}`heap.variables.stack_discipline`: a slot is removed only after all
slots allocated after it have been removed.

```{rule} Heap:Step.allocVariable
\frac{
  \begin{gathered}
    x \notin \operatorname{dom}(V) \\
    V' = (x:\bot)::V
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
store. Allocation pushes exactly that slot, initially uninitialized, ahead of
all existing slots. It preserves their order and contents and the object map.

The operation supplies the identity; the successful-step rule checks its
availability. The execution layer is also responsible for the stronger
{anchor-ref}`heap.variables.lifetimes` requirement: distinct allocation lifetimes
receive distinct identities. Absence from the current store alone does not prove
that an identity has never been used.

```{rule} Heap:Step.deallocVariable
\frac{
  \begin{gathered}
    V = (x:\bot)::V'
  \end{gathered}
}{
  \langle O,V \rangle
  \xrightarrow{\mathsf{deallocVariable}(x)}
  \langle O,V' \rangle
}
\;\text{DeallocVariable}
```

{anchor}`heap.variables.deallocate`
Deallocating a variable requires the newest live slot to be that variable and
to be uninitialized. It pops that slot and preserves all remaining slots in
their existing order, as well as every object. An absent slot, an initialized
slot, or an older slot beneath a newer one cannot be deallocated.

{anchor}`heap.variables.release_before_deallocation`
Deallocation does not release a reference implicitly. If a variable still
contains a reference when its scope ends, that reference must first be released
and the slot made uninitialized. Dropping a variable's contents and removing its
slot are separate operations.

````{example} Heap:nested_variables
Starting from the empty state:

1. Allocate variable `x`, creating an uninitialized slot.
2. Allocate a distinct variable `y`, also uninitialized.
3. Deallocate `y`, leaving `x` unchanged.

Immediately before step 3, `y` is above `x`. Trying to deallocate `x` at that
point has no successful step, even though both slots are uninitialized. After
step 3, the state again contains only the uninitialized slot `x` and no objects:

```{heap}
vars = variables()
vars.x = uninitialized()
```

Finally, deallocate `x` to return to the empty state. The Lean case uses runtime
identities zero and one and checks both the successful sequence and rejection
of removing `x` while `y` is live.
````

{informational} This checks the heap operations needed for empty nested bindings.
Using and releasing initialized contents, generating fresh identities, and
arranging lexical cleanup still require execution rules. The heap already
requires last-in-first-out deallocation of the allocated slots.

{informational} The Lean selector provides each rule for hand comparison.
Its `objects`, `variables`, and `id` correspond to \\(O,V,x\\).
`insertFresh` prepends a fresh entry. For deallocation, `empty` proves that the
slot is uninitialized and `top` proves that its identity is first in the store;
with these premises, `erase` removes exactly the first entry. Together these
conditions correspond to \\(V=(x:\bot)::V'\\). The mathematical view omits
proof terms but retains their conditions.
Correspondence between the views remains a review obligation.

The declarations and proofs live in `lean/Heap.lean`. The
`allocVariable_contents` and `deallocVariable_contents` lemmas characterize the
resulting variable stores exactly. The corresponding `*_preserves_objects` lemmas
prove that the object map is unchanged; `deallocVariable_rejects_initialized`
and `deallocVariable_rejects_absent` distinguish an empty slot from an initialized
or missing one. `allocVariable_pushes` and `deallocVariable_pops` characterize
the stack updates, and `deallocVariable_rejects_non_top` excludes removing any
older slot while a newer one remains live.
These proofs do not establish global freshness across executions, call or scope
semantics, or the later ownership invariants.

## Object creation

Creation takes an allocated destination variable \\(x\\) and the contents or
shape of the new object. The new object's identity \\(\alpha\\) is chosen by
the transition; it is not an argument of the operation.

{anchor}`heap.create.destination`
Every creation operation requires that its destination variable exists and is
uninitialized. It replaces that empty slot with an owned reference to the new
object. Creation neither allocates a variable slot nor overwrites a reference.

{anchor}`heap.create.fresh`
The new object identity is absent from the current object map. Creation adds an
object at that identity without replacing an existing object.

We write \\(O[\alpha \mapsto o]\\) for fresh extension of the object map, and
\\(V[x \mapsto r]\\) for replacement of the existing destination's contents.
The preconditions distinguish extension from replacement. Every other
association remains unchanged. Replacing a variable's contents preserves its
position in the store, even when newer slots are allocated above it.

### Primitives

```{rule} Heap:Step.createPrimitive
\frac{
  \begin{gathered}
    V(x) = \bot \\
    \alpha \notin \operatorname{dom}(O) \\
    O' = O[\alpha \mapsto \mathsf{primitive}(v)] \\
    V' = V[x \mapsto \mathsf{owned}(\alpha)]
  \end{gathered}
}{
  \langle O,V \rangle
  \xrightarrow{\mathsf{createPrimitive}(v,x)}
  \langle O',V' \rangle
}
\;\text{CreatePrimitive}
```

{anchor}`heap.create.primitive`
Creating a primitive stores exactly the supplied value \\(v \in P\\). The
machine does not interpret that value while allocating its object.

```{example} Heap:integer_primitive
Start with the empty state and allocate variable `x`. Performing
`createPrimitive(22, x)` creates a single primitive object containing the integer
`22` and puts its owned reference in `x`. The value `22` is the object's payload;
`x` contains a reference to that object.
```

### Aggregates

For a sequence of pairwise distinct field names \\({\overline f}\\),
\\(\lbrace f \mapsto \bot \mid f \in {\overline f}\rbrace\\) is the map containing exactly
those fields, each uninitialized.

```{rule} Heap:Step.createAggregate
\frac{
  \begin{gathered}
    V(x) = \bot \\
    \alpha \notin \operatorname{dom}(O) \\
    \operatorname{distinct}({\overline f}) \\
    M = \{f \mapsto \bot \mid f \in {\overline f}\} \\
    O' = O[\alpha \mapsto \mathsf{aggregate}(M)] \\
    V' = V[x \mapsto \mathsf{owned}(\alpha)]
  \end{gathered}
}{
  \langle O,V \rangle
  \xrightarrow{\mathsf{createAggregate}({\overline f},x)}
  \langle O',V' \rangle
}
\;\text{CreateAggregate}
```

{anchor}`heap.create.aggregate`
Creating an aggregate supplies a finite sequence of distinct field names. The
new object's field map contains exactly those fields, all uninitialized. An
empty sequence creates an aggregate with no fields. A sequence containing a
duplicate field name has no successful creation step.

```{example} Heap:aggregate_fields
Start with the empty state and allocate variable `x`. Performing
`createAggregate(["x", "y"], x)` creates a single aggregate with two field slots,
both uninitialized, and puts its owned reference in `x`. The quoted `"x"` is a
field name; the final `x` is the destination variable. Neither field contains a
reference yet.
```

### Arrays

Write \\(\bot^n\\) for the sequence of exactly \\(n\\) uninitialized slots.
In particular, \\(\bot^0\\) is the empty sequence.

```{rule} Heap:Step.createArray
\frac{
  \begin{gathered}
    V(x) = \bot \\
    \alpha \notin \operatorname{dom}(O) \\
    O' = O[\alpha \mapsto \mathsf{array}(\bot^n)] \\
    V' = V[x \mapsto \mathsf{owned}(\alpha)]
  \end{gathered}
}{
  \langle O,V \rangle
  \xrightarrow{\mathsf{createArray}(n,x)}
  \langle O',V' \rangle
}
\;\text{CreateArray}
```

{anchor}`heap.create.array`
Creating an array supplies a nonnegative length \\(n\\). The new array contains
exactly \\(n\\) slots, all uninitialized; zero-length arrays are permitted.
The creation step does not inspect or manufacture a primitive value to represent
the length.

```{example} Heap:array_slots
Start with the empty state and allocate variable `x`. Performing
`createArray(2, x)` creates a single array with two slots, at indices zero and one,
and puts its owned reference in `x`. Both slots are uninitialized: the array has
length two even though neither slot contains a reference yet.
```

{anchor}`heap.create.locality`
Each creation step adds exactly one object and initializes exactly its destination
variable. It preserves every existing object, every other variable's contents,
and the order of allocated variable identities. No fields or array elements in
the new object contain references.

{informational} In Lean, `insertFresh` extends the object map and `replace`
updates the already allocated destination without changing the variable keys
or their order.
`initialFields` constructs the aggregate's empty field slots, and `initialElements`
uses `Array.replicate` for the array's empty element slots. The fresh identity and
proofs of the preconditions are arguments of the rule, not extra arguments of the operation.
The mathematical view retains those conditions while omitting their proof terms.

The checked `createPrimitive_effects`, `createAggregate_effects`, and
`createArray_effects` lemmas characterize each update. `initialFields_contents`
proves the aggregate's exact field contents; `initialElements_size` and
`initialElements_contents` prove the array's length and uninitialized elements.
`creation_preserves_variable_order` proves that creation retains the exact
sequence of variable identities.
The `creation_rejects_absent` and `creation_rejects_initialized` lemmas exclude
invalid destinations, while `createAggregate_rejects_duplicate_fields` excludes
duplicate field names. These are local facts about successful-step derivations,
not a definition of fault execution. The
[checked creation examples](examples.md#checked-creation-examples) assert complete
successor states for primitive creation, aggregates, and arrays,
including the empty cases.

Freshness here only concerns the current object map. It does not yet specify
identity reuse after destruction or invalidate pre-existing dangling references
in an arbitrary malformed state. The candidate
{anchor-ref}`heap.ownership.exclusive` and
{anchor-ref}`heap.references.valid_target` properties require a broader argument
about reachable states and the remaining operations.

{informational} Variable allocation, variable deallocation, and the three object
creation operations are now formalized. Reference transfer, release, and lease
invalidation remain under design. The prose below guides future rules; it is
not an implementation of `drop` or function calls.

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

{informational} Proposed example: giving from an access path into a temporary
variable is written:

```text
S ──give(p.items[3], tmp)──▶ S′
```

Here `p.items[3]` is the access path, and `tmp` identifies the allocated
destination variable. A `give` rule and a Lean test for this example remain to
be written; the notation does not yet assert a successful transition.

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
cascade through owning fields. Scope cleanup removes variable slots in reverse
allocation order, releasing each slot's contents before deallocating it.
Destruction order within objects, cycles, and invalid borrowed
references encountered during cleanup require explicit decisions before
defining a total algorithm.
