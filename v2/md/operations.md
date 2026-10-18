# Operations on the machine

[Setting the stage](state.md#setting-the-stage) introduces the machine state,
its components, the initial configuration, and well-formedness conditions.
This chapter defines transitions that allocate and deallocate variables and
create objects. [Place operations](place-operations.md) defines transitions
through access paths.

```{definition} PathOperations:MachineStep
{anchor}`heap.steps.judgment`
Successful execution of a heap operation is a transition between machine states:

\\[
S \xrightarrow{\omega} S'
\\]

Performing \\(\omega\\) in state \\(S\\) can take one machine step to state
\\(S'\\). The operation label includes its explicit arguments. For each fixed
\\(\omega\\), this is a relation on pairs of states; there is no separate
returned value outside the successor state.

The relation combines the allocation and creation rules with the path-based
rules. Its Lean definition calls these `Heap.Step` and `PathStep`, respectively;
our operation labels omit the `heap` and `place` wrappers.
```

[Place operations](place-operations.md) explains how a path's effective permission
determines giving, leasing, sharing, and dropping.

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

This chapter's operation grammar covers variable lifetimes and object
creation; the place-operation grammar is in the next chapter. Each creation
operation requires an allocated, uninitialized destination
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

Variables are introduced individually, so entering a block does not require
knowing all of its slots in advance. Allocation pushes an uninitialized slot;
deallocation removes only the newest slot. These transitions obey
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
availability. Absence from the current store does not record a previous
allocation history. The [execution-layer obligations](#scope-and-binding-lifetimes)
address source bindings and identity reuse.

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

```{lemma} Heap:deallocVariable_requires_empty
{anchor}`heap.variables.release_before_deallocation`
Deallocation requires an uninitialized variable slot:

\\[
\langle O,V\rangle\xrightarrow{\mathsf{deallocVariable}(x)} S'
\;\Longrightarrow\; V(x)=\bot
\\]

It does not release a reference implicitly. If a variable still contains a
reference when its scope ends, that reference must first be released and the
slot made uninitialized. Releasing contents and removing the slot are separate
operations.

**Proof outline.** The deallocation rule has an explicit premise that the
selected variable contains the uninitialized slot.
```

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

### Stack discipline

The following lemmas make the stack behavior explicit. They hold for every
successful allocation or deallocation, without requiring well-formedness.

```{lemma} Heap:allocVariable_pushes
Allocation adds an uninitialized slot at the front of the variable store.

\\[
\langle O,V\rangle\xrightarrow{\mathsf{allocVariable}(x)}\langle O',V'\rangle
\;\Longrightarrow\; V'=(x:\bot)::V
\\]

**Proof outline.** The allocation rule inserts the new entry at the head of the
store. Its fresh-identity premise rules out replacing an existing slot.
```

```{lemma} Heap:deallocVariable_pops
{anchor}`heap.variables.stack_discipline`
Deallocation removes exactly the newest live slot, which must be uninitialized.
In particular, it cannot remove an older slot while a newer slot is still live.

\\[
\langle O,V\rangle\xrightarrow{\mathsf{deallocVariable}(x)}\langle O',V'\rangle
\;\Longrightarrow\; V=(x:\bot)::V'
\\]

**Proof outline.** The rule requires the first identity to be \\(x\\), and
requires its slot to be uninitialized. Unique keys identify the head entry;
erasing it leaves precisely the tail of the store.
```

```{lemma} PathOperations:PathStep.preserves_variable_order
Place operations preserve the ordered list of variable identities.
Here \\(\mathsf{ids}(V)\\) lists identities in store order.

\\[
\langle O,V\rangle\xrightarrow{\omega}_{\mathsf{place}}\langle O',V'\rangle
\;\Longrightarrow\;\mathsf{ids}(V')=\mathsf{ids}(V)
\\]

**Proof outline.** Consider each place operation. Writing or clearing a slot,
retargeting a lease, and destroying an object do not insert, delete, or reorder
variable slots. Each case follows from the corresponding storage effect.
```

### Scope and binding lifetimes

{obligation}`heap.variables.alpha_renaming`
The execution semantics must assign runtime identities to source bindings so
that shadowing and separate function invocations have distinct live slots.
Function calls α-rename parameters and local bindings to fresh identities.
The execution layer also determines visibility and arranges cleanup in reverse
allocation order, leaving a caller's slots below its callee's slots.
The heap's stack lemmas support this discipline; call and scope rules remain to
be formalized.

{obligation}`heap.variables.lifetimes`
Retiring a binding and later allocating a slot must not revive a reference to
the retired binding. The [well-formedness slot condition](state.md#well-formed-states)
constrains references within one state. Non-revival also relates different
moments of an execution; it needs a freshness or invalidation policy. Using
fresh identities for binding lifetimes is one way to meet that obligation.
The current heap checks only absence from the live variable store.

## Object creation

Creation takes an allocated destination variable \\(x\\) and the contents or
shape of the new object. The new object's identity \\(\alpha\\) is chosen by
the transition; it is not an argument of the operation.

```{lemma} Heap:creation_requires_empty
{anchor}`heap.create.destination`
Every creation operation requires that its destination variable \\(x\\) exists
and is uninitialized:

\\[
\langle O,V\rangle\xrightarrow{\mathsf{create}(\ldots,x)} S'
\;\Longrightarrow\; V(x)=\bot
\\]

Here \\(\mathsf{create}\\) ranges over primitive, aggregate, and array creation.
A creation operation cannot use an absent destination or overwrite a reference.

**Proof outline.** Each of the three creation rules has the same premise: the
destination occurs in the variable store with an uninitialized slot.
```

The creation rules below replace that empty slot with an owned reference to the
new object.

{anchor}`heap.create.fresh`
The new object identity is absent from the current object map. Creation adds an
object at that identity without replacing an existing object.

```{definition} Heap:FiniteMap.insertFresh Heap:FiniteMap.replace
{anchor}`heap.maps.updates`
We write \\(O[\alpha \mapsto o]\\) for fresh extension of the object map, and
\\(V[x \mapsto r]\\) for replacement of the existing destination's contents.
Fresh extension requires \\(\alpha\notin\operatorname{dom}(O)\\); replacement
here requires \\(x\in\operatorname{dom}(V)\\). Every other association remains
unchanged. Replacing a variable's contents preserves its position in the store,
even when newer slots are allocated above it.
```

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

```{definition} Heap:initialFields
{anchor}`heap.create.initial_fields`
For a sequence of pairwise distinct field names \\({\overline f}\\),
\\(\lbrace f \mapsto \bot \mid f \in {\overline f}\rbrace\\) is the map containing
exactly those fields, each uninitialized. The empty sequence gives an empty map.
```

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

```{definition} Heap:initialElements
{anchor}`heap.create.initial_elements`
Write \\(\bot^n\\) for the sequence of exactly \\(n\\) uninitialized slots.
In particular, \\(\bot^0\\) is the empty sequence.
```

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
in an arbitrary malformed state. The [ownership invariant](properties.md#ownership-accounting) additionally excludes
dangling owners and has a checked preservation proof for all these steps.
The {anchor-ref}`heap.references.valid_target` obligation still needs lifetime
rules and a well-formedness preservation proof; lease activity is a separate
property from finite reference resolution.

The next chapter, [Place operations](place-operations.md), defines transitions
for give, lease, share, and drop, together with their reference and cleanup
effects. Borrow invalidation, complete scope cleanup, and function-call
execution remain to be specified.

### Array shape

{obligation}`heap.arrays.fixed_length`
An array's length is specified at creation and should remain unchanged while
that object lives. Slot updates may change its elements without changing their
index domain. A preservation theorem across all machine operations remains to
be stated and proved.
