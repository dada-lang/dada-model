# Objects, references, and frames

{anchor}`heap.primitives.parameter`
The heap model as a whole is parameterized by a set \\(P\\) of primitive
values. This parameter is fixed throughout a machine execution and is implicit
in every definition and judgment.

{anchor}`heap.primitives.opaque`
The heap machine treats primitive values as opaque. Arithmetic and
primitive-specific interpretation belong to the client of the machine.

{example} The client can choose integers as its set of primitive values.

We use single letters for the components of a machine state. Object identities
\\(\alpha, \beta\\) and frame identities \\(\iota\\) belong to distinct sets;
\\(f\\) is a field name, \\(x\\) a binding name, \\(v\\) a primitive value, and
\\(n\\) a nonnegative index:

```{grammar} Heap:ObjectId Heap:FrameId Heap:FieldName Heap:BindingName
\begin{array}{rcl}
\alpha,\beta &\in& \mathsf{ObjectId} \\
\iota &\in& \mathsf{FrameId} \\
f &\in& \mathsf{FieldName} \\
x &\in& \mathsf{BindingName} \\
v &\in& P \\
n &\in& \mathbb{N}
\end{array}
```

An overbar denotes a finite ordered sequence, including the empty sequence.
\\(K \rightharpoonup V\\) denotes a finite map from keys in \\(K\\) to values in
\\(V\\). We write \\(M\\) for a field map, \\(B\\) for a binding map, \\(O\\)
for the object map, and \\(F\\) for the frame map:

```{grammar} Heap:FiniteMap Heap:Object Heap:Frame Heap:State
\begin{array}{rcl}
M &\in& \mathsf{FieldName} \rightharpoonup \mathsf{Slot} \\
B &\in& \mathsf{BindingName} \rightharpoonup \mathsf{Slot} \\
O &\in& \mathsf{ObjectId} \rightharpoonup \mathsf{Object} \\
F &\in& \mathsf{FrameId} \rightharpoonup \mathsf{Frame}
\end{array}
```

Objects \\(o\\) contain primitive values, field maps, or sequences of slots.
A slot \\(s\\) is uninitialized, written \\(\bot\\), or contains a reference
\\(r\\). A frame \\(b\\) holds a binding map. A state \\(S\\) pairs its object
map with its frame map:

```{grammar} Heap:Object Heap:Slot Heap:Frame Heap:State
\begin{array}{rcl}
o &::=& \mathsf{primitive}(v) \\
  &\mid& \mathsf{aggregate}(M) \\
  &\mid& \mathsf{array}(\overline{s}) \\[.5em]
s &::=& \bot \mid r \\[.5em]
b &::=& \mathsf{frame}(B) \\[.5em]
S &::=& \langle O,F \rangle
\end{array}
```

References \\(r\\) target either an object or a place \\(p\\). A place names
one runtime slot: a binding in a frame, a field of an object, or an array element.
Object and frame identities distinguish \\(\alpha.f\\) from \\(\iota.x\\):

```{grammar} Heap:Reference Heap:Place
\begin{array}{rcl}
r &::=& \mathsf{owned}(\alpha) \\
  &\mid& \mathsf{leased}(p) \\
  &\mid& \mathsf{showned}(\alpha) \\
  &\mid& \mathsf{shlease}(\alpha) \\[.5em]
p &::=& \iota.x \mid \alpha.f \mid \alpha[n]
\end{array}
```

{informational} These mathematical definitions stand on their own; each selector
links them to the corresponding Lean declarations for comparison. The notation
\\(\bot\\) corresponds to `Slot.uninitialized`, and a reference used as a slot
corresponds to `Slot.initialized`. \\(P\\) corresponds to `Primitive`; the
mathematical sequences and finite maps leave their storage representation to the
formalization. The build checks these citations, not the correspondence between
the two presentations.

## Fields contain references to objects

A primitive is an object, not a special scalar payload of a field. Thus a point
can have owned fields targeting two primitive objects:

```{heap}
main = frame()
α = object(Point, "α")
β = primitive(22, "β")
γ = primitive(44, "γ")
main.p = owned(α)
α.x = owned(β)
α.y = owned(γ)
```

`Point` is an explanatory label here; whether aggregate objects carry type labels
in the formal machine is open. The object identities do not prescribe allocation
boundaries or observable identity comparison.

Frames group local bindings. A frame in this account does not prescribe a
physical stack layout. Bindings and fields have the same slot contents.
Temporary frame bindings will account for intermediate results, so a reference
cannot disappear from ownership accounting between operations.

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
Thus `α.f` names a field slot, `main.p` names a frame binding, and `items[0]`
names an array element. How moves, replacement, and sublease promotion update
or invalidate these dependencies remains to be specified.

{anchor}`heap.references.shlease_targets`
A shlease targets an object, not the edge through which it was created. Its
validity need not depend on the survival of a particular showned handle.

{example} The lease below joins the owning edge `α.f`, while the shlease
points directly to `β`:

```{heap}
main = frame()
α = object(Container)
β = primitive(22)
main.p = owned(α)
α.f = owned(β)
main.q = lease(α.f)
main.r = shlease(β)
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

An access path \\(a\\) starts at a binding name and follows a finite sequence
of projections \\(\overline{\pi}\\). Each projection selects a field or an
array element:

```{grammar} Heap:AccessPath Heap:Projection
\begin{array}{rcl}
a &::=& x\,\overline{\pi} \\
\pi &::=& .f \mid [n]
\end{array}
```

An operation supplies the frame in which to resolve the initial binding.
The path does not itself contain a frame identity.

{example} `main: p.items[3].x` selects binding `p` in frame `main`, then
projects field `items`, element `3`, and field `x`.

{anchor}`heap.paths.resolution`
Successful resolution of an access path in a frame selects a place \\(p\\): the
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
