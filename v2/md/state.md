# Objects, references, and frames

{anchor}`heap.primitives.parameter`
The heap model as a whole is parameterized by a set `Primitive` of primitive
values. This parameter is fixed throughout a machine execution and is implicit
in every definition and judgment; we do not thread it through individual type names.

{anchor}`heap.primitives.opaque`
The heap machine treats primitive values as opaque. Arithmetic and
primitive-specific interpretation belong to the client of the machine.

{example} The client can choose integers as its set of primitive values.

The following declarations are included directly from `lean/Heap.lean`.
`Primitive` is a section variable in that file; Lean infers it as a parameter
of declarations that use it. IDs are distinct wrapper types.

```{lean.type}
Heap:ObjectId
Heap:FrameId
Heap:FieldName
Heap:BindingName
Heap:Object
Heap:Slot
Heap:Reference
Heap:Place
Heap:Frame
Heap:State
```

{informational} In the grammar view, an overbar denotes a finite ordered sequence
(both Lean `List` and `Array`); `K ⇀ V` denotes a finite map from keys `K` to
values `V`. The Lean view retains the exact container representation.

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
The argument is a `Place`: the runtime slot holding that supporting reference.
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
its `Primitive` parameter.

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

An operation selects a binding in a frame followed by projections:

```{lean.type}
Heap:AccessPath
Heap:Projection
```

{example} `main: p.items[3].x` selects binding `p` in frame `main`, then
projects field `items`, element `3`, and field `x`.

{anchor}`heap.paths.resolution`
Successful resolution of an access path in a frame selects a `Place`: the
runtime slot on which the operation acts.

{anchor}`heap.references.lease_stores_place`
A unique lease stores its supporting `Place`, not the access path used to reach
that slot. Its target is the unique reference specified by
{anchor-ref}`heap.references.lease_targets`.

{anchor}`heap.paths.access_depends_on_route`
The access available through a path depends on the references traversed along
that path. Two paths reaching the same object can therefore confer different access.

{anchor}`heap.paths.shared_traversal`
Traversing a shared reference constrains access to the selected field even when
that field contains an owned reference.
