# Objects, references, and variables

## Setting the stage

The machine state records allocated objects and the slots that hold references.
We describe that state first, then the objects, references, and variables within it.

```{definition} Heap:State
{anchor}`heap.state.components`
A state \\(S\\) consists of an object map \\(O\\) and an ordered variable
store \\(V\\). The object map associates each object identity \\(\alpha\\)
with its contents. The variable store associates each runtime variable identity
\\(x\\) with a slot and records the order in which those slots were allocated,
newest first:

\\[
S ::= \langle O,V \rangle
\\]
```

Slots also occur inside objects, as aggregate fields or array elements. Each
slot is either uninitialized or holds a reference. Thus \\(S\\) accounts for
references throughout the object map as well as in all live variables, including
temporaries and suspended callers' variables.

```{definition} Invariants:AllocatedObject
{anchor}`heap.state.allocated_objects`
An object is *allocated* when its identity belongs to
\\(\operatorname{dom}(O)\\), the set of identities in the object map.
Likewise, \\(\operatorname{dom}(V)\\) is the set of allocated variable
identities. An allocated slot can be uninitialized. Below, we define an object's
*liveness* by an owning path from a variable; well-formedness will require every
allocated object to be live.
```

```{definition} Heap:State.initial Heap:FiniteMap.empty
{anchor}`heap.state.initial`
The initial state is \\(S_0=\langle\varnothing,\epsilon\rangle\\): an empty
object map and an empty variable store. We use \\(\epsilon\\) for the empty
sequence.
```

We will define well-formedness as a property of a state after introducing its
components. The [operations chapter](operations.md) defines transitions between
states; preservation of well-formedness is a separate question.

## Objects and slots

{anchor}`heap.primitives.parameter`
The heap model as a whole is parameterized by a set \\(P\\) of primitive
values. This parameter is fixed throughout a machine execution and is implicit
in every definition and judgment.

{anchor}`heap.primitives.opaque`
The heap machine treats primitive values as opaque. Arithmetic and
primitive-specific interpretation belong to the client of the machine.

We use single letters for the components of the state. Object identities
\\(\alpha, \beta\\) and variable identities \\(x,y\\) belong to distinct sets;
\\(f\\) is a field name, \\(v\\) a primitive value, and
\\(n\\) a nonnegative index:

```{grammar} Heap:ObjectId Heap:VariableId Heap:FieldName
\begin{array}{rcl}
\alpha,\beta &\in& \mathsf{ObjectId} \\
x,y &\in& \mathsf{VariableId} \\
f &\in& \mathsf{FieldName} \\
v &\in& P \\
n &\in& \mathbb{N}
\end{array}
```

References \\(r\\) target either an object or a place \\(p\\). A place names
one runtime slot: a variable, a field of an object, or an array element.
Object and variable identities distinguish \\(\alpha.f\\) from \\(x\\):

```{grammar} Heap:Reference Heap:Place
\begin{array}{rcl}
r &::=& \mathsf{owned}(\alpha) \\
  &\mid& \mathsf{leased}(p) \\
  &\mid& \mathsf{showned}(\alpha) \\
  &\mid& \mathsf{shlease}(\alpha) \\[.5em]
p &::=& x \mid \alpha.f \mid \alpha[n]
\end{array}
```

A slot \\(s\in\mathsf{Slot}\\) is either uninitialized, written \\(\bot\\), or
contains a reference \\(r\\). Variables, aggregate fields, and array elements
all use this same slot type:

```{grammar} Heap:Slot
s ::= \bot \mid r
```

An overbar denotes a finite ordered sequence, including the empty sequence.
\\(K \rightharpoonup T\\) denotes a finite map from keys in \\(K\\) to values in
\\(T\\). An object \\(o\in\mathsf{Object}\\) contains a primitive value, an
aggregate field map \\(M\\), or a sequence of slots:

```{grammar} Heap:FiniteMap Heap:Object
\begin{array}{rcl}
M &\in& \mathsf{FieldName} \rightharpoonup \mathsf{Slot} \\[.5em]
o &::=& \mathsf{primitive}(v) \\
  &\mid& \mathsf{aggregate}(M) \\
  &\mid& \mathsf{array}({\overline s})
\end{array}
```

In \\(\mathsf{aggregate}(M)\\), \\(\operatorname{dom}(M)\\) is the set of
fields that exist. If \\(M(f)=\bot\\), field \\(f\\) exists but is
uninitialized; if \\(f\notin\operatorname{dom}(M)\\), the aggregate has no
such field. [Aggregate creation](operations.md#aggregates) specifies the complete
set of field names up front and creates a slot for each, all initially
uninitialized.

The object map \\(O\\) associates object identities with objects. The variable
store \\(V\\) is an ordered sequence of slots with distinct variable identities.
The notation \\((x:s)::V\\) places slot \\(x\\), containing \\(s\\), at the front
of the store:

```{grammar} Heap:FiniteMap Heap:State
\begin{array}{rcl}
O &\in& \mathsf{ObjectId} \rightharpoonup \mathsf{Object} \\
V &::=& \epsilon \mid (x:s)::V
\end{array}
```

```{definition} Places:readSlot Invariants:Stored
{anchor}`heap.state.slot_lookup`
The partial lookup \\(S(p)\\) reads **slot contents**, not an object. Its result
is either \\(\bot\\) or a reference \\(r\\). A reference leads to an object
identity \\(\alpha\\); the separate lookup \\(O(\alpha)\\) reads that object's
contents \\(o\\).

For \\(S=\langle O,V\rangle\\), slot lookup is defined by the shape of the place:

- \\(S(x)=V(x)\\) for an allocated variable \\(x\\).
- \\(S(\alpha.f)=M(f)\\) when \\(O(\alpha)=\mathsf{aggregate}(M)\\)
  and field \\(f\\) exists.
- \\(S(\alpha[n])=s_n\\) when \\(O(\alpha)=\mathsf{array}({\overline s})\\)
  and \\(0\le n<|{\overline s}|\\).

We write \\(S(p)=s\\) when this lookup is defined and returns slot contents
\\(s\\). In particular, \\(S(p)=\bot\\) denotes an existing, uninitialized
slot. Lookup is undefined at an absent variable or object, a missing field,
an out-of-bounds element, or a place whose object has the wrong shape.
```

## Runtime variables

```{definition} Heap:VariableId Heap:Place
{anchor}`heap.variables.identity`
A variable identity names a runtime slot, separately from the source-level name
of a binding. The execution layer maps source bindings to these identities;
its [scope and α-renaming obligations](operations.md#scope-and-binding-lifetimes)
are stated with the operations.
```

```{definition} Heap:State Invariants:Stored
{anchor}`heap.variables.store`
The variable store contains all live variable slots, including those belonging
to suspended callers. Every initialized slot participates in ownership
accounting, whether or not the currently executing code can access it. The heap
state has no frame map or distinguished active frame.
```

```{lemma} Invariants:Stored.value_unique
A place has at most one slot value. In particular, a runtime variable identity
cannot name two different contents in one state.

\\[
S(p)=s \land S(p)=t \;\Longrightarrow\; s=t
\\]

**Proof outline.** Variable and field maps have distinct keys. An array index
selects a single element. Consider the three forms of place and apply the
corresponding uniqueness fact.
```

## Fields contain references to objects

A primitive is an object, not a special scalar payload of a field. Thus a point
can have owned fields targeting two primitive objects:

{informational} Proposed example: this is the intended result of constructing a
point. [Creation examples](examples.md#checked-creation-examples) check the
individual allocations, but transfer into fields is not yet formalized, so the
complete construction has no Lean test yet.

```{heap}
vars = variables()
α = object(Point, "α")
β = primitive(22, "β")
γ = primitive(44, "γ")
vars.p = owned(α)
α.x = owned(β)
α.y = owned(γ)
```

`Point` is an explanatory label here; whether aggregate objects carry type labels
in the formal machine is open. The object identities do not prescribe allocation
boundaries or observable identity comparison.

Variables and fields have the same slot contents. Temporary variables account
for intermediate results, so a reference cannot disappear from ownership
accounting between operations. The diagram groups variable slots in a box
labeled “Variables”; `vars.p` in its facts denotes variable `p`, with `vars`
serving only to name that presentation group.

## Four reference kinds

| Kind | Meaning |
| --- | --- |
| `owned` | Unique ownership |
| `leased` | Unique lease |
| `showned` | Shared ownership |
| `shlease` | Shared lease |

Ownership keeps an object alive; leases do not. `shlease` and `showned` are vocabulary of this
operational model, not proposed first-class terms in Dada's surface language.

```{definition} Heap:Reference
{anchor}`heap.references.object_targets`
Owned, showned, and shlease references target objects. Two showned references
can independently own the same object.
```

```{definition} Invariants:OwnerAt Invariants:ReferenceAt
{anchor}`heap.references.owner_occurrence`
Ownership is counted across **all variable slots, aggregate fields, and array
elements**. Equal references stored in different slots are separate occurrences.
Write \\(\mathsf{owner}_S(p,\alpha)\\) when \\(S(p)\\) is either
\\(\mathsf{owned}(\alpha)\\) or \\(\mathsf{showned}(\alpha)\\).
Leases do not count as owners.
```

```{definition} Heap:Reference Access:ResolveReference
{anchor}`heap.references.lease_targets`
A unique lease stores its supporting place \\(p\\), the runtime slot holding
the reference from which the lease derives. For example, \\(\mathsf{leased}(\alpha.f)\\)
uses the reference in field \\(f\\) of object \\(\alpha\\) as its support.
Resolving it follows a finite chain of leased references to an owned reference;
each supporting slot must exist and be initialized.
```

When a reference moves to another slot, its direct dependent leases are
retargeted to the destination, wherever those leases are stored. Descendants
keep their intermediate supporting places. The checked
[move rules](place-operations.md) implement this update; replacement,
invalidation, and dead-link promotion still need lifetime rules.

```{definition} Heap:Reference Access:ResolveReference
{anchor}`heap.references.shlease_targets`
A shlease targets an object, not the edge through which it was created. Its
validity need not depend on the survival of a particular showned handle.
```

{informational} Proposed example: the lease below joins the owning edge `α.f`,
while the shlease points directly to `β`. Lease creation and path permissions
have checked rules, but active-borrow validity remains unfinished. This combined diagram still has no
corresponding machine-transition test:

```{heap}
vars = variables()
α = object(Container)
β = primitive(22)
vars.p = owned(α)
α.f = owned(β)
vars.q = lease(α.f)
vars.r = shlease(β)
```

{informational} The sketch does not yet encode invalidation or the active status of a lease.
The [open questions](questions.md) track those remaining decisions.

## Well-formed states

Well-formedness describes one state, independently of how it was produced.
We first define what keeps an object live and how a reference reaches it.

```{definition} WellFormed:OwningReachable
{anchor}`heap.state.live_objects`
The **live objects** \\(L(S)\\) are the object identities reached by finite
**owning paths** starting at variable slots:

1. An `owned` or `showned` reference in a variable makes its target live.
2. An `owned` or `showned` reference in a field or array element of a live object
   makes its target live as well.

These clauses generate the smallest such set. All allocated variables are roots,
including temporaries and suspended callers' variables. Leases do not keep
objects alive, and a cycle with no owning path from a variable is not live.
```

```{definition} Access:ResolveReference
{anchor}`heap.references.resolution`
Resolving a reference \\(r\\) finds an object identity \\(\alpha\\), written
\\(r\leadsto_S\alpha\\).

- `owned`, `showned`, and `shlease` contain their target identity directly.
  Resolution succeeds when that object is allocated.
- `leased` names a supporting slot. Resolution follows the reference in that
  slot through a finite chain of leases ending in an `owned` reference.
  Every supporting slot must exist and hold the required reference.

The three lookups have distinct results:

\\[
S(p)=r\qquad r\leadsto_S\alpha\qquad O(\alpha)=o
\\]

Reading the slot gives a reference \\(r\\); following it gives an identity
\\(\alpha\\); looking up that identity gives object contents \\(o\\).
Missing objects, empty or missing support slots, and support cycles cannot
resolve. The [access-path judgment](place-operations.md#resolving-an-access-path)
also tracks permission along an access route.
```

```{definition} WellFormed:WellFormed
{anchor}`heap.state.well_formed`
A state \\(S=\langle O,V\rangle\\) is **well-formed**, written
\\(\mathsf{WF}(S)\\), when:

1. **Every allocated object is live.** Each \\(\alpha\in\operatorname{dom}(O)\\)
   has an owning path from a variable.
2. **Every existing slot is uninitialized or resolves to a live object.**
   Its contents are either \\(\bot\\), or a reference \\(r\\) with
   \\(r\leadsto_S\alpha\\) and \\(\alpha\in L(S)\\).
3. **A unique owner is the sole owner.** If \\(S(p)=\mathsf{owned}(\alpha)\\),
   no other slot holds either an `owned` or a `showned` reference to \\(\alpha\\).

The slot condition covers every variable, aggregate field, and array element.
It requires each stored reference to resolve successfully, so a broken reference
cannot be overlooked simply because no path through it succeeds. Leases do not
count as owners; these clauses do not establish which lease is active.
```

### Consequences

```{lemma} WellFormed:WellFormed.has_owner
{anchor}`heap.ownership.has_owner`
Every allocated object in a well-formed state has an owning reference somewhere
in the state:

\\[
\mathsf{WF}(S)\land\alpha\in\operatorname{dom}(O)
\;\Longrightarrow\;\exists p.\;\mathsf{owner}_S(p,\alpha)
\\]

**Proof outline.** Clause 1 supplies a finite owning path. Its last reference
is an owner of the object.
```

```{lemma} WellFormed:WellFormed.unique_owner
{anchor}`heap.ownership.unique_is_sole`
If a slot holds a unique owner, it is the only owning occurrence of that object:

\\[
\begin{gathered}
\mathsf{WF}(S)\land S(p)=\mathsf{owned}(\alpha) \\
\Longrightarrow\quad \forall q.\;\mathsf{owner}_S(q,\alpha)\iff q=p
\end{gathered}
\\]

**Proof outline.** Clause 3 excludes every other slot. The reference at
\\(p\\) itself is an owner.
```

Thus every allocated object has either one unique owner or one or more shared
owners. A unique owner may coexist with leases to its object.

```{lemma} WellFormed:WellFormed.lease_support_exists
A unique lease stored in a well-formed state has an initialized supporting slot:

\\[
\begin{gathered}
\mathsf{WF}(S)\land S(p)=\mathsf{leased}(q) \\
\Longrightarrow\quad\exists r.\; S(q)=r
\end{gathered}
\\]

**Proof outline.** Clause 2 requires the lease to resolve. Its first resolution
step reads a reference from the supporting slot.
```

```{definition} WellFormed:ReferenceReachable
{anchor}`heap.state.reference_reachable`
Write \\(R(S)\\) for the objects reached from variable slots by following
references of **any kind**, continuing through fields and array elements.
Each reference must resolve successfully, and paths are finite. This describes
structural reachability; permission to perform an operation is a separate question.
```

```{lemma} WellFormed:WellFormed.reachability_agrees
The allocated, live, and reference-reachable objects in a well-formed state
are exactly the same:

\\[
\mathsf{WF}(S)\;\Longrightarrow\;
\operatorname{dom}(O)=L(S)=R(S)
\\]

**Proof outline.** Clause 1 gives \\(\operatorname{dom}(O)\subseteq L(S)\\).
By clause 2, every owning reference resolves, so an owning path is also a
reference path: \\(L(S)\subseteq R(S)\\). Successful resolution reaches
allocated objects, giving \\(R(S)\subseteq\operatorname{dom}(O)\\).
```

```{example} WellFormed:disconnected_owning_cycle_not_wellFormed
Let the variable store be empty and let the only allocated object be an
aggregate whose `self` field owns that same object:

\\[
O=\{\alpha\mapsto\mathsf{aggregate}(\{\mathsf{self}\mapsto
\mathsf{owned}(\alpha)\})\},\qquad V=\epsilon
\\]

The object has exactly one owner and its reference reaches an allocated object,
but there is no owning path from a variable. Thus \\(L(S)=\varnothing\\):
the state fails clause 1, and its initialized field also fails clause 2 because
its target is not live.
```

Well-formedness constrains the current state. Preventing identity reuse from
reviving a stale reference is a separate
[binding-lifetime obligation](operations.md#scope-and-binding-lifetimes).

### Well-formedness and reachability

```{definition} PathOperations:MachineReachable
{anchor}`heap.state.reachable`
A state is *reachable* if a finite execution leads to it from the empty state
\\(S_0\\). The definition has two cases: the empty execution reaches
\\(S_0\\), and one more successful step extends an existing execution.
Here \\(S\xrightarrow{\omega}S'\\) is the machine-step judgment defined in
[Operations on the machine](operations.md).

\\[
\begin{gathered}
\frac{}{\mathsf{Reachable}(S_0)}\;\text{Initial} \\[1em]
\frac{\mathsf{Reachable}(S)\qquad S\xrightarrow{\omega}S'}{
 \mathsf{Reachable}(S')}\;\text{Step}
\end{gathered}
\\]
```

Reachability of a **state** describes an execution history. The sets \\(L(S)\\)
and \\(R(S)\\) instead describe paths within a single state. Well-formedness
constrains that state. The [preservation chapter](properties.md) proves that
the current operations preserve ownership. Full well-formedness preservation remains a
proof obligation: the current drop rules can leave a dangling shared lease.

## Arrays and uninitialized slots

```{definition} Heap:Object Heap:Place
{anchor}`heap.arrays.indices`
An array contains a finite sequence of slots. Its element places use nonnegative
indices, numbered from zero up to but excluding the sequence's length.

{anchor}`heap.arrays.length_counts_slots`
Length counts every slot, including uninitialized slots.

{anchor}`heap.arrays.structural_numbers`
Array lengths and indices are structural numbers of the machine, independent of
its primitive-value parameter \\(P\\).
```

An array's length is specified at creation. The
[operations chapter](operations.md#array-shape) states the fixed-length obligation.

{informational} This deliberately narrow array interface is intended to admit a JVM array
implementation: [fixed length](https://docs.oracle.com/javase/specs/jls/se20/html/jls-10.html),
indexed access, and a length operation. How the
abstract uninitialized state maps to a backend's initialization requirements is
a separate representation question; it is not permission to read uninitialized
storage. See [backend goals](dada/tenets.md#tracing-friendly-execution).

```{lemma} Invariants:Stored.uninitialized_has_no_reference
{anchor}`heap.slots.uninitialized`
Uninitialized slots contain no reference and therefore contribute no ownership.

\\[
S(p)=\bot\;\Longrightarrow\;\neg\exists r.\; S(p)=r
\\]

**Proof outline.** A place has one slot value. The uninitialized form and the
form containing a reference are distinct constructors of a slot.
```

{informational} Creating an aggregate or array with uninitialized slots lets us discuss construction,
partial moves, and unsafe operations without making every object fully
initialized at every step.

## Access paths

An access path \\(a\\) starts at a variable identity and follows a finite sequence
of projections \\({\overline \pi}\\). Each projection selects a field or an
array element:

```{grammar} Heap:AccessPath Heap:Projection
\begin{array}{rcl}
a &::=& x\,{\overline \pi} \\
\pi &::=& .f \mid [n]
\end{array}
```

The initial variable is looked up directly in the variable store.

{informational} Proposed resolution example: `p.items[3].x` starts at runtime
variable `p`, then projects field `items`, element `3`, and field `x`. Here `p` is
a readable label for a runtime identity, not a source name requiring lexical
resolution. The [path-resolution rules](place-operations.md#resolving-an-access-path)
define each projection; a Lean test of this complete traversal remains to be written.

```{definition} Access:ResolvePath
{anchor}`heap.paths.resolution`
Successful resolution of an access path in a state selects a place \\(p\\): the
runtime slot on which the operation acts.
```

```{definition} Heap:Reference Heap:AccessPath
{anchor}`heap.references.lease_stores_place`
A unique lease stores its supporting place, not the access path used to reach
that slot. Its target is the unique reference specified by
{anchor-ref}`heap.references.lease_targets`.
```

```{definition} Access:ResolvePath Access:AccessPermission.project
{anchor}`heap.paths.access_depends_on_route`
The access available through a path depends on the references traversed along
that path. Two paths reaching the same object can therefore confer different access.
```

```{lemma} Access:AccessPermission.shared_owned_not_given
{anchor}`heap.paths.shared_traversal`
Traversing an owned reference under shared access cannot restore the `given`
permission needed to transfer unique ownership.

**Proof outline.** Projecting an owned reference preserves the incoming
permission. Neither `showned` nor `shlease` is `given`.
```
