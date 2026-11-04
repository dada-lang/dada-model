# Assignment

## Refill a field

````{example} assignment.example.refill
:lean: Assignment/Checks:refill

An empty field can receive a new value. Suppose `w` has type
`given Wrapper.{-resource}`, with these declarations:

```dada
class Resource {}
class Wrapper { resource: Resource }

store w.resource, new Resource();
```

The statement checks, and `w` has the whole type `given Wrapper` afterwards.
The core spelling `store p, e` installs the value of `e` into the slot `p`.
It does not call a destructor for the previous contents.
The [negative view entry](given-typing.md#claim-given.typing.views)
records that `resource` exists and is empty.
````

## Replace a class explicitly

````{example} assignment.example.replacement
:lean: Assignment/Checks:explicit_replacement

Use [explicit destruction](destructors.md#claim-destructors.drop_typing)
before storing over an owned class. With an initialized `r: given Resource`
and `replacement: given Resource`, this sequence checks:

```dada
class Resource {
    drop { let Resource → {} = self→; }
}

drop r;
store r, replacement→;
```

The destructor consumes the old resource. The store then moves the replacement
into the empty `r` slot, leaving `replacement` empty. During the destructor
call, the replacement remains rooted in the suspended caller frame.
The example checks the destructor declaration and the two-statement sequence;
it assumes the two initial bindings.
````

````{example} assignment.example.boundaries
:lean: Assignment/Checks:class_replacement

An occupied class field cannot be overwritten, even when its class declares a
destructor. Given whole `w: given Wrapper`, this store is rejected:

```dada
store w.resource, new Resource();
```

An empty local retains its declared storage type. An empty `r` that previously
held a `Resource` accepts another `Resource`, but rejects a `Token`:

```dada
class Token {}
store r, new Resource(); // accepted from the empty-r state
store r, new Token();    // rejected even from the empty-r state
```

These are separate checks from the same initial state.
````

## Structs and shared references

````{example} assignment.example.structs
:lean: Assignment/Checks:structs

Struct replacement needs no destructor call. Consider these declarations:

```dada
struct Point {}
shared struct SharedPoint {}
struct Box { point: Point }
```

The following cases check independently:

| Destination's current type | Store | Result |
| --- | --- | --- |
| `p: given Point` | `store p, new Point()` | accepted |
| `s: shared SharedPoint` | `store s, new SharedPoint()` | accepted |
| `b: given Box` | `store b.point, new Point()` | accepted |
| `b: shared Box` | store a shared `Point` into `b.point` | rejected |

A local slot holding a shared reference is writable. A field reached through
shared access is not. Overwriting a struct reference does not run user code;
[collection](functions.md#claim-functions.gc) reclaims its object
only if no frame can still reach it.

This layer fixes a local's permission as well as its nominal type: a local
inferred as `given Point` does not accept a `shared Point`. This is a typing
restriction, not a layout requirement. Both permissions have the same nominal
layout key.
````

## Partial values keep their views

````{example} assignment.example.partial
:lean: Assignment/Checks:partial_value

Storing a partial value does not repair its missing fields. An empty local `w`
with fixed storage type `given Wrapper` can receive a
`given Wrapper.{-resource}` value; afterwards its current type is still
`given Wrapper.{-resource}`. It cannot be left behind when the frame finishes:
the [class-consumption obligation](destructors.md#claim-destructors.finished_environment)
also applies to partial classes.

[Unpacking](shared-typing.md#claim-shared.typing.bindings) remains an alternative
to repairing the container. The pattern `Wrapper → { resource: r }` gives the
empty `r` binding a fixed storage type `given Resource`, obtained from the
field declaration. Its current slot is empty, but it has not become untyped.
````

````{example} assignment.example.rhs
:lean: Assignment/Checks:rhs_first

The right-hand side runs before the destination is checked. For whole
`w: given Wrapper`, this statement moves `w` out, then refills the same local:

```dada
store w, w→;
```

It checks and leaves `w` whole. Conversely, an empty `w` does not provide a
writable `w.resource` slot: a field store needs an initialized parent after
right-hand-side evaluation. Nominal knowledge of the field name is insufficient.
````

## Syntax and fixed binding types

```{definition} assignment.syntax
:lean: Assignment/Syntax:Statement Assignment/Syntax:Body Assignment/Syntax:Declaration Assignment/Syntax:Program

A statement adds `store p, e;` to the [Destructor statements](destructors.md#claim-destructors.declarations).
Here `p` is a [place](shared.md#claim-shared.syntax) and `e` is a
[Shared value expression](shared.md#claim-shared.syntax). Calls remain
statements with fresh result bindings; a call is not an assignment expression.
Bodies, declarations, and programs have the same components as in Destructors,
with statement lists drawn from this extended syntax.
```

```{definition} assignment.context
:lean: Assignment/StorageTypes:StorageType Assignment/StorageTypes:storageType Assignment/StorageTypes:layoutKey Assignment/StorageTypes:Context Assignment/StorageTypes:Context.WellFormed Assignment/Typing:initialContext Assignment/Typing:bindingTypes

A storage type is a nominal type name paired with a permission. Taking the
storage type of a current value type forgets its view. Its layout key forgets
the permission too; `given Foo` and `shared Foo` have the same key.

A typing context contains two ordered maps with the same local names:

* **Fixed binding types** retain each local's nominal type and permission.
* **Current descriptions** record either an empty slot or its present value
  type, including the view.

The current environment must be [well formed](shared-typing.md#claim-shared.typing.environments).
Each fixed type must be [admissible](shared-typing.md#claim-shared.typing.well_formed_types) as a whole type. Every initialized current
description must agree with its binding's fixed nominal type and permission.
Empty descriptions carry no value view, but their fixed binding types remain.

Parameters begin with their declared fixed types and whole current types.
A fresh variable binding infers its fixed type from its initializer's type.
Unpacking obtains fixed types from the nominal field declarations in pattern
order, including for fields that are currently empty.
```

## Static store operation

```{definition} assignment.view
:lean: Assignment/StorageTypes:replaceView
:uses: assignment.context

Replacing the view at a field path keeps all entries outside that subtree.
A positive ancestor is expanded along the destination path so its unaffected
siblings remain exposed. Entries beneath the overwritten path are removed;
the incoming value's entries are prefixed by that path and inserted. Finally,
the result is [normalized](given-typing.md#claim-given.typing.normalization).
The root nominal type and permission do not change. Incoming negative entries
stay negative; an omitted interior does not become whole.
```

```{definition} assignment.store
:lean: Assignment/StorageTypes:replaceable Assignment/StorageTypes:storeCurrent Assignment/StorageTypes:store
:uses: assignment.context assignment.view

The static store operation takes a [context](#claim-assignment.context) **after** expression evaluation, a
destination place, and an incoming value type. It returns an updated context,
or fails. The input context and incoming type must be well formed and
admissible respectively.

For a local destination, its fixed type must match the incoming nominal type
and permission. Its current slot must be empty or have a struct type.

For a field destination, the root must be initialized and the parent path must
be accessible with `given` permission. The declared field type must match the
incoming nominal type and permission. The [current field description](shared-typing.md#claim-shared.typing.field) must be
known and either empty or a struct. An omitted, inaccessible field cannot be
written merely because its declaration is known. The root's view is updated
using [view replacement](#claim-assignment.view).

The operation preserves the fixed binding map and requires the resulting
context to be well formed. It accepts partial incoming views. It never
implicitly consumes an occupied class, including a partial class.
```

```{definition} assignment.typing
:lean: Assignment/Typing:ExprTyped Assignment/Typing:ArgsTyped Assignment/Typing:BindingTyped Assignment/Typing:LocalTyped Assignment/Typing:StatementTyped
:uses: assignment.context assignment.store assignment.syntax

Expression and argument typing use the existing [Shared judgments](shared-typing.md#claim-shared.typing.expressions) on the
current environment, retaining fixed bindings and requiring the resulting
context to be well formed. Binding typing uses [Shared's binding judgment](shared-typing.md#claim-shared.typing.bindings) and
extends the fixed map with the [binding types](#claim-assignment.context).
A local statement evaluates its initializer, then binds it.

A store statement first types its expression, producing an incoming type and
an intermediate context. It then applies the [static store operation](#claim-assignment.store)
to that intermediate context. The operation's output is the statement's
output context. Thus an expression may empty the destination before the store,
but cannot leave a missing ancestor along a field destination.

Calls and struct drops retain their Destructor rules, using these extended
contexts. A call still requires a declared callee, correctly typed arguments,
and a fresh destination matching its result signature.
```

```{theorem} assignment.fixed
:lean: Assignment/StorageTypes:store_preserves_bindings
:uses: assignment.store

Every successful [static store](#claim-assignment.store) preserves the entire fixed binding map.
```

## Execution

```{definition} assignment.write
:lean: Assignment/Write:Writable Assignment/Write:Replaceable Assignment/Write:Write
:uses: assignment.syntax

A writable slot is either a local entry (initialized or empty), or a field of
an object reached through a uniquely accessible parent place. Resolving a
field destination resolves the parent, not the field's previous contents.

Runtime contents are replaceable if the slot is empty or holds a struct
reference. Writing installs the incoming reference into the selected slot;
it preserves object identities, field names, other slots, and the allocation
counter. In particular, it does not reallocate the parent object.
```

```{definition} assignment.machine
:lean: Assignment/Step:Frame Assignment/Step:Configuration Assignment/Step:RawStep Assignment/Step:Step Assignment/Step:Configuration.collect
:uses: assignment.write assignment.syntax

The machine retains the [explicit stack and eager collector](functions.md#claim-functions.gc).
Each frame owns its locals, remaining body, and result destination. Expressions
run against the top frame; collection uses the roots of **all** frames.

For a raw store transition:

1. Evaluate the right-hand-side expression to a reference and intermediate state.
2. Resolve a writable destination slot in that intermediate state.
3. Check that its previous contents are replaceable.
4. Write the incoming reference into that slot and advance the statement list.

The resulting configuration is then collected. There is no collection between
evaluation and installation of the incoming reference. Explicit drops remain
separate statements, with their own calls and collection steps. Return and
initial-frame exit retain the requirement that no class root remains in the
completed frame.
```

```{example} assignment.example.gc
:lean: Assignment/ExecutionChecks:struct_collection
:uses: assignment.machine

Replacing a local shared-struct reference can make the old object unreachable.
The checked transition begins with `s` referencing `SharedPoint` object 0,
constructs object 1, and stores its reference in `s`. In the resulting raw
configuration, object 0 is unreachable and object 1 is reachable. The eager
collector therefore discards object 0 and retains object 1.
```

```{example} assignment.example.age
:lean: Assignment/ExecutionChecks:younger_child
:uses: assignment.machine

Refilling a field can reverse allocation-age order. In the checked step,
`w` owns wrapper object 1 with an empty `resource` field. The store constructs
resource object 2 and installs it in object 1. Both objects survive collection,
and their identities remain 1 and 2.

This resulting heap satisfies the [structural heap invariant](shared.md#claim-shared.well_formed):
its objects are rooted and its owning references are compatible. It does not
satisfy the stronger requirement that every field target have a smaller allocation
index than its parent. The foundation deliberately does not require that ordering.
```

## Correspondence and proof boundary

```{definition} assignment.embedding
:lean: Correspondence/DestructorsAssignment:statement Correspondence/DestructorsAssignment:body Correspondence/DestructorsAssignment:declaration Correspondence/DestructorsAssignment:declarations Correspondence/DestructorsAssignment:frame Correspondence/DestructorsAssignment:configuration
:uses: assignment.syntax assignment.machine

Embedding Destructors into Assignment maps statements, bodies, declarations,
and frames componentwise. It adds no store statements. Heap objects, allocation
counters, local slots, call names, and value expressions remain unchanged.
```

```{theorem} assignment.forward
:lean: Correspondence/DestructorsAssignment:step_forward
:uses: assignment.embedding

Every Destructor execution step is preserved by this [embedding](#claim-assignment.embedding), including
collection and frame transitions, with the declaration table embedded as well.
This is an operational correspondence result; it does not assert preservation
of typing with the new fixed binding metadata.
```

```{future-note} assignment.safety.next
:uses: assignment.example.age assignment.forward

The [static rules](#claim-assignment.typing) and [operational rules](#claim-assignment.machine) above are formalized, with checked examples.
Assignment does not yet have a general progress/preservation theorem, a proof
that its collector retains all owned class objects, or a reverse execution
correspondence theorem. Those are the next proof obligations. The existing
soundness theorems for Given, Shared, Functions, and Destructors remain about
those earlier languages.

The foundation now uses rootedness and ownership compatibility rather than
allocation-age order. The [refill example](#claim-assignment.example.age) satisfies
that invariant without changing object IDs. The next task is to prove that all
typed stores preserve the invariant and the typing realization, not merely this
particular transition.

Surface `p = e` elaboration and automatic destructor insertion remain deferred.
Mutable leases and their different representation also remain outside this layer.
```

## Appendix: inherited calls and completion

```{definition} assignment.completion
:lean: Assignment/Typing:ResultTyped Assignment/Typing:DestinationTyped Assignment/Typing:Finished Assignment/Typing:DropTyped Assignment/Typing:SequenceTyped Assignment/Typing:BodyTyped Assignment/Typing:DeclarationsTyped Assignment/Typing:ProgramTyped
:uses: assignment.typing

Result typing evaluates an optional result against the [signature](functions.md#claim-functions.signatures). Destination
typing either accepts no result and no destination, or introduces a fresh local
with the result's declared fixed type. Sequence typing composes statement
contexts in order.

A body starts in its [parameter context](#claim-assignment.context), checks its statements and result, and
must finish with only empty or struct locals. This condition uses current
descriptions, so an empty class slot is permitted while an initialized partial
class is not. Class drops use whole given receivers and the dedicated destructor
name; struct drops give and discard without invoking user code.

Declaration tables have distinct names and check every signature and body
against the entire table, permitting recursion. A program additionally requires
a well-formed class table and a main sequence starting in the empty context
and satisfying the same completion condition. Recursion has no termination
requirement.
```
