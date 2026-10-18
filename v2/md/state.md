# Objects, references, and variables

{anchor}`heap.primitives.parameter`
The heap model as a whole is parameterized by a set \\(P\\) of primitive
values. This parameter is fixed throughout a machine execution and is implicit
in every definition and judgment.

{anchor}`heap.primitives.opaque`
The heap machine treats primitive values as opaque. Arithmetic and
primitive-specific interpretation belong to the client of the machine.

```{example} Heap:integer_primitive
The client can choose integers as its set of primitive values. Starting from the
empty state, allocate variable `x`, then perform `createPrimitive(22, x)`. The
result contains a primitive object holding exactly `22`, and `x` holds its owned
reference. The Lean case fixes both identities to index zero in their distinct
identity types and checks the complete resulting state.
```

We use single letters for the components of a machine state. Object identities
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

An overbar denotes a finite ordered sequence, including the empty sequence.
\\(K \rightharpoonup T\\) denotes a finite map from keys in \\(K\\) to values in
\\(T\\). We write \\(M\\) for a field map and \\(O\\) for the object map.
The variable store \\(V\\) is an ordered sequence of slots with distinct
variable identities. The empty store is \\(\epsilon\\); \\((x:s)::V\\)
places slot \\(x\\), containing \\(s\\), at the front of the store:

```{grammar} Heap:FiniteMap Heap:Object Heap:State
\begin{array}{rcl}
M &\in& \mathsf{FieldName} \rightharpoonup \mathsf{Slot} \\
O &\in& \mathsf{ObjectId} \rightharpoonup \mathsf{Object} \\
V &::=& \epsilon \mid (x:s)::V
\end{array}
```

Objects \\(o\\) contain primitive values, field maps, or sequences of slots.
A slot \\(s\\) is uninitialized, written \\(\bot\\), or contains a reference
\\(r\\). A state \\(S\\) pairs its object map with its variable store:

```{grammar} Heap:Object Heap:Slot Heap:State
\begin{array}{rcl}
o &::=& \mathsf{primitive}(v) \\
  &\mid& \mathsf{aggregate}(M) \\
  &\mid& \mathsf{array}({\overline s}) \\[.5em]
s &::=& \bot \mid r \\[.5em]
S &::=& \langle O,V \rangle
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

{informational} These mathematical definitions stand on their own; each selector
links them to the corresponding Lean declarations for comparison. The notation
\\(\bot\\) corresponds to `Slot.uninitialized`, and a reference used as a slot
corresponds to `Slot.initialized`. \\(P\\) corresponds to `Primitive`; the
mathematical sequences and finite maps leave their storage representation to the
formalization. Lean also represents the variable store with `FiniteMap`, but
its entry order is significant: newest allocations come first. The build checks
these citations, not the correspondence between the two presentations.

## Runtime variables and scope

{anchor}`heap.variables.identity`
A variable identity names one runtime slot. It is separate from the source-level
name of a binding: shadowing and separate invocations of a function use distinct
identities, even when their source names are the same.

{anchor}`heap.variables.store`
The variable store contains all live variable slots, including those belonging
to suspended callers. Every initialized slot participates in ownership
accounting, whether or not the currently executing code can access it. The heap
state has no frame map or distinguished active frame.

{anchor}`heap.variables.stack_discipline`
Variable slots follow a stack discipline. Allocation pushes a fresh,
uninitialized slot onto the front of the store. Deallocation can remove only
the most recently allocated slot that is still live, and that slot must be
uninitialized. Updating a slot's contents preserves its position, so even an
empty outer slot cannot be removed while a newer slot remains allocated.

{anchor}`heap.variables.alpha_renaming`
The execution layer assigns fresh runtime identities when bindings are introduced.
Function calls α-rename their parameters and local bindings to fresh identities;
nested scopes likewise distinguish newly introduced bindings from outer ones.
The execution layer determines which identities are accessible and arranges
scope cleanup to obey the heap's stack discipline. A caller's slots remain
below its callee's slots until the callee has removed them.

{anchor}`heap.variables.lifetimes`
Distinct allocation lifetimes use distinct variable identities. An identity
removed from the variable store must not be reused to make an earlier lease
refer to a new slot.

{informational} These are requirements on the execution layer that will drive
the heap operations. That layer, including call and scope rules, is not yet
formalized. The current allocation rule checks absence from the live variable
store; it does not record previously used identities or enforce the lifetime
freshness requirement on its own. Lease invalidation on slot removal also
remains to be defined.

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

{anchor}`heap.references.object_targets`
Owned, showned, and shlease references target objects. Two showned references
can independently own the same object.

{anchor}`heap.references.lease_targets`
A unique lease targets the unique edge (owned or leased) from which it derives.
We write `lease(α.f)` for a lease of the edge in field `f` of object `α`.
The argument is a place \\(p\\): the runtime slot holding that supporting reference.
Thus `α.f` names a field slot, `x` names a variable slot, and `items[0]`
names an array element. How moves, replacement, and sublease promotion update
or invalidate these dependencies remains to be specified.

{anchor}`heap.references.shlease_targets`
A shlease targets an object, not the edge through which it was created. Its
validity need not depend on the survival of a particular showned handle.

{informational} Proposed example: the lease below joins the owning edge `α.f`,
while the shlease points directly to `β`. Lease creation and validity are not yet
formalized, so this diagram has no corresponding transition test yet:

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

## Arrays and uninitialized slots

{anchor}`heap.arrays.indices`
Arrays have integer-indexed slots, numbered from zero up to but excluding their length.

{anchor}`heap.arrays.fixed_length`
An array's length is specified at creation and does not change during its lifetime.

{anchor}`heap.arrays.length_counts_slots`
Length counts every slot, including uninitialized slots.

{anchor}`heap.arrays.structural_numbers`
Array lengths and indices are structural numbers of the machine, independent of
its primitive-value parameter \\(P\\).

{informational} This deliberately narrow array interface is intended to admit a JVM array
implementation: [fixed length](https://docs.oracle.com/javase/specs/jls/se20/html/jls-10.html),
indexed access, and a length operation. How the
abstract uninitialized state maps to a backend's initialization requirements is
a separate representation question; it is not permission to read uninitialized
storage. See [backend goals](dada/tenets.md#tracing-friendly-execution).

{anchor}`heap.slots.uninitialized`
Uninitialized slots contain no reference and contribute no ownership.

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
resolution. The path grammar is defined, but resolution transitions and a Lean
test of this traversal remain to be written.

{anchor}`heap.paths.resolution`
Successful resolution of an access path in a state selects a place \\(p\\): the
runtime slot on which the operation acts.

{anchor}`heap.references.lease_stores_place`
A unique lease stores its supporting place, not the access path used to reach
that slot. Its target is the unique reference specified by
{anchor-ref}`heap.references.lease_targets`.

{anchor}`heap.paths.access_depends_on_route`
The access available through a path depends on the references traversed along
that path. Two paths reaching the same object can therefore confer different access.

{anchor}`heap.paths.shared_traversal`
Traversing a shared reference constrains access to the selected field even when
that field contains an owned reference.
