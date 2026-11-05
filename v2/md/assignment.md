# Assignment

## Refill a field

````{example} assignment.example.refill
:lean: Assignment/Checks:refill

An empty field can receive a new value. Suppose `w` has type
`given Wrapper.{-resource}`, with these declarations:

```dada
class Resource {}
class Wrapper { resource: Resource }

w.resource = new Resource();
```

The statement checks, and `w` has the whole type `given Wrapper` afterwards.
The assignment `p = e` installs the value of `e` into the slot `p`.
It does not call a [destructor](destructors.md#claim-destructors.declarations)
for the previous contents.
The [negative view entry](given-typing.md#claim-given.typing.views)
records that `resource` exists and is empty.
````

## A complete replacement lifetime

````{example} assignment.example.refill_safety
:lean: Assignment/SafetyChecks:refill_safety

The same [frame](functions.md#claim-functions.machine) can retain a partial wrapper
across a [destructor call](destructors.md#claim-destructors.execution), refill
its field, and then consume both the wrapper and the replacement:

```dada
class Resource {
    drop { let Resource → {} = self→; }
}
class Wrapper { resource: Resource }

let w = new Wrapper(new Resource());
drop w.resource;
w.resource = new Resource();
let Wrapper → { resource: r } = w→;
drop r;
```

This checks as a complete program, including the destructor body and the
initial frame's [consumption obligation](destructors.md#claim-destructors.finished_environment).
`Wrapper` needs no destructor because the program explicitly
[unpacks it](shared-typing.md#claim-shared.typing.bindings). Every finite
[execution, defined below](#claim-assignment.execution), is safe: each reached
state either has no frames or can take another step. If all frames have exited,
the heap is empty.
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
r = replacement→;
```

The destructor consumes the old resource. The store then moves the replacement
into the empty `r` slot, leaving `replacement` empty. During the destructor
call, the replacement remains rooted in the
[suspended caller frame](functions.md#claim-functions.machine).
The example checks the destructor declaration and the two-statement sequence;
it assumes the two initial bindings.
````

````{example} assignment.example.boundaries
:lean: Assignment/Checks:class_replacement

An occupied class field cannot be overwritten, even when its class declares a
[destructor](destructors.md#claim-destructors.declarations). Given whole `w: given Wrapper`, this store is rejected:

```dada
w.resource = new Resource();
```

An empty local retains its declared storage type. An empty `r` that previously
held a `Resource` accepts another `Resource`, but rejects a `Token`:

```dada
class Token {}
r = new Resource(); // accepted from the empty-r state
r = new Token();    // rejected even from the empty-r state
```

These are separate checks from the same initial state.
````

## Structs and shared references

````{example} assignment.example.structs
:lean: Assignment/Checks:structs

[Struct](shared.md#claim-shared.struct) replacement needs no destructor call.
Consider these declarations:

```dada
struct Point {}
shared struct SharedPoint {}
struct Box { point: Point }
```

The following cases check independently:

| Destination's current type | Assignment | Result |
| --- | --- | --- |
| `p: given Point` | `p = new Point()` | accepted |
| `s: shared SharedPoint` | `s = new SharedPoint()` | accepted |
| `b: given Box` | `b.point = new Point()` | accepted |
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

````{example} assignment.example.overwrite_safety
:lean: Assignment/SafetyChecks:overwrite_safety

A [shared-struct](shared.md#claim-shared.declarations) local can instead be
overwritten and left for [collection](functions.md#claim-functions.gc):

```dada
shared struct SharedPoint {}
let s = new SharedPoint();
s = new SharedPoint();
```

This also checks as a complete program. For every finite
[execution, defined below](#claim-assignment.execution), each reached state
either has no frames or can take another step; no frames means an empty heap.
The [completion obligation](destructors.md#claim-destructors.finished_environment)
permits `s` to remain initialized, so it needs no explicit drop.
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
`w: given Wrapper`, [giving](shared-typing.md#claim-shared.typing.giving) moves
`w` out, then the store refills the same local:

```dada
w = w→;
```

It checks and leaves `w` whole. Conversely, an empty `w` does not provide a
writable `w.resource` slot: a field store needs an initialized parent after
right-hand-side evaluation. Nominal knowledge of the field name is insufficient.
````

## Syntax and fixed binding types

```{definition} assignment.syntax
:lean: Assignment/Syntax:Statement Assignment/Syntax:Body Assignment/Syntax:Declaration Assignment/Syntax:Program

Assignment adds the statement `p = e;` to the [Destructor statements](destructors.md#claim-destructors.declarations).
Here `p` is a [place](shared.md#claim-shared.syntax) and `e` is a
[Shared value expression](shared.md#claim-shared.syntax). Calls remain
statements with fresh result bindings; a call is not an assignment expression.
Bodies, declarations, and programs have the same components as in Destructors,
with statement lists drawn from this extended syntax.
```

```{definition} assignment.context
:lean: Assignment/StorageTypes:StorageType Assignment/StorageTypes:storageType Assignment/StorageTypes:layoutKey Assignment/StorageTypes:Context Assignment/StorageTypes:Context.WellFormed Assignment/Typing:initialContext Assignment/Typing:bindingTypes

A *storage type* is a nominal type name paired with a
[permission](shared-typing.md#claim-shared.typing.types). Taking the storage type
of a current value type forgets its [view](given-typing.md#claim-given.typing.views). Its layout key forgets
the permission too; `given Foo` and `shared Foo` have the same key.

A typing context contains two ordered maps with the same local names:

* **Fixed binding types** retain each local's nominal type and permission.
* **Current descriptions** record either an empty slot or its present value
  type, including the view.

The current environment must be [well formed](shared-typing.md#claim-shared.typing.environments).
Each fixed type must be [well formed](shared-typing.md#claim-shared.typing.well_formed_types)
and [normalized](shared-typing.md#claim-shared.typing.normalization) as a whole type.
Every initialized current
description must agree with its binding's fixed nominal type and permission.
Empty descriptions carry no value view, but their fixed binding types remain.

Parameters begin with their declared fixed types and whole current types.
A fresh variable binding infers its fixed type from its initializer's type.
[Unpacking](shared-typing.md#claim-shared.typing.bindings) obtains fixed types
from the nominal field declarations in pattern
order, including for fields that are currently empty.
```

## Static store operation

```{definition} assignment.view
:lean: Assignment/StorageTypes:replaceView
:uses: assignment.context

Replacing the [view](given-typing.md#claim-given.typing.views) at a field path
keeps all entries outside that subtree.
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

The static store operation takes a [context](#claim-assignment.context) **after**
[expression evaluation](shared.md#claim-shared.evaluation), a destination
[place](shared.md#claim-shared.syntax), and an incoming value type. It returns an updated context,
or fails. The input context must be well formed. The incoming type must be
[well formed](shared-typing.md#claim-shared.typing.well_formed_types) and
[normalized](shared-typing.md#claim-shared.typing.normalization).

For a local destination, its fixed type must match the incoming nominal type
and permission. Its current slot must be empty or have a
[struct type](shared.md#claim-shared.struct).

For a field destination, the root must be initialized and the parent path must
[focus](shared-typing.md#claim-shared.typing.focus) to a type with `given` permission. The declared field type must match the
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

[Calls and struct drops](destructors.md#claim-destructors.execution) retain
their Destructor rules, using these extended
contexts. A call still requires a declared callee, correctly typed arguments,
and a fresh destination matching its result signature.
```

```{theorem} assignment.fixed
:lean: Assignment/StorageTypes:store_preserves_bindings
:uses: assignment.store

Every successful [static store](#claim-assignment.store) preserves the entire [fixed binding map](#claim-assignment.context).
```

## Execution

```{definition} assignment.write
:lean: Assignment/Write:Writable Assignment/Write:Replaceable Assignment/Write:Write
:uses: assignment.syntax

A writable slot is either a local entry (initialized or empty), or a field of
an object reached through a uniquely accessible parent
[place](shared.md#claim-shared.syntax). [Resolving](shared.md#claim-shared.resolution)
a field destination resolves the parent, not the field's previous contents.

Runtime contents are replaceable if the slot is empty or holds a reference to a
[struct](shared.md#claim-shared.struct). Writing installs the incoming reference into the selected slot;
it preserves object identities, field names, other slots, and the allocation
counter. In particular, it does not reallocate the parent object.
```

```{definition} assignment.machine
:lean: Assignment/Step:Frame Assignment/Step:Configuration Assignment/Step:RawStep Assignment/Step:Step Assignment/Step:Configuration.collect
:uses: assignment.write assignment.syntax

The machine retains the [explicit stack](functions.md#claim-functions.machine)
and [eager collector](functions.md#claim-functions.gc).
Each frame owns its locals, remaining body, and result destination. Expressions
run against the top frame; collection uses the roots of **all** frames.

For a raw store transition:

1. [Evaluate](shared.md#claim-shared.evaluation) the right-hand-side expression
   to a reference and intermediate state.
2. Resolve a [writable destination slot](#claim-assignment.write) in that intermediate state.
3. Check that its previous contents are [replaceable](#claim-assignment.write).
4. [Write](#claim-assignment.write) the incoming reference into that slot and advance the statement list.

The resulting configuration is then collected. There is no collection between
evaluation and installation of the incoming reference.
[Explicit drops](destructors.md#claim-destructors.execution) remain
separate statements, with their own calls and collection steps. Return and
initial-frame exit retain the [requirement that no class root remains](destructors.md#claim-destructors.finished_environment)
in the completed frame.
```

```{definition} assignment.execution
:lean: Assignment/Step:Configuration.initial Assignment/Step:Steps
:uses: assignment.syntax assignment.machine

A *finite execution* is zero or more [machine steps](#claim-assignment.machine).
A program starts with an empty heap and one initial [frame](#claim-assignment.machine)
containing its main statements and no locals or result destination.
```

```{definition} assignment.finished
:lean: Assignment/Step:Configuration.finished
:uses: assignment.machine

A configuration is *finished* when its [frame stack](#claim-assignment.machine)
is empty.
```

```{definition} assignment.stuck
:lean: Assignment/Step:Stuck
:uses: assignment.finished assignment.machine

A configuration is *stuck* when it is not [finished](#claim-assignment.finished)
and has no possible next [machine step](#claim-assignment.machine). A finished
configuration is therefore not stuck.
```

```{example} assignment.example.gc
:lean: Assignment/ExecutionChecks:struct_collection
:uses: assignment.machine

Replacing a local [shared-struct](shared.md#claim-shared.declarations) reference
can make the old object unreachable.
The checked transition begins with `s` referencing `SharedPoint` object 0,
constructs object 1, and stores its reference in `s`. In the resulting raw
configuration, object 0 is unreachable and object 1 is reachable. The eager
[collector](#claim-assignment.machine) therefore discards object 0 and retains object 1.
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

## Correspondence

```{definition} assignment.embedding
:lean: Correspondence/DestructorsAssignment:statement Correspondence/DestructorsAssignment:body Correspondence/DestructorsAssignment:declaration Correspondence/DestructorsAssignment:declarations Correspondence/DestructorsAssignment:frame Correspondence/DestructorsAssignment:configuration
:uses: assignment.syntax assignment.machine

Embedding Destructors into Assignment maps
[statements, bodies, and declarations](#claim-assignment.syntax), and
[frames](#claim-assignment.machine) componentwise. It adds no store statements. Heap objects, allocation
counters, local slots, call names, and value expressions remain unchanged.
```

```{theorem} assignment.forward
:lean: Correspondence/DestructorsAssignment:step_forward
:uses: assignment.embedding

Every [Destructor execution step](destructors.md#claim-destructors.execution)
is preserved by this [embedding](#claim-assignment.embedding), including
collection and frame transitions, with the declaration table embedded as well.
This is an operational correspondence result; it does not assert preservation
of typing with the new fixed binding metadata.
```

```{future-note} assignment.safety.next
:uses: assignment.example.age assignment.forward

Reverse execution correspondence and preservation of Destructor typing with
the new fixed binding metadata remain separate proof obligations. The
[forward execution theorem](#claim-assignment.forward) does not establish either.

Automatic destructor insertion remains deferred.
Mutable leases and their different representation also remain outside this layer.
```

## Appendix: inherited calls and completion

```{definition} assignment.completion
:lean: Assignment/Typing:ResultTyped Assignment/Typing:DestinationTyped Assignment/Typing:SequenceTyped
:uses: assignment.typing assignment.context

*Result typing* evaluates an optional result against the
[signature](functions.md#claim-functions.signatures). *Destination typing*
either accepts no result and no destination, or introduces a fresh local with
the result's declared [fixed type](#claim-assignment.context). *Sequence typing*
composes [statement contexts](#claim-assignment.typing) in order.
```

```{definition} assignment.body_typing
:lean: Assignment/Typing:Finished Assignment/Typing:DropTyped Assignment/Typing:BodyTyped
:uses: assignment.completion assignment.context assignment.typing

A *well-typed body* starts in its [parameter context](#claim-assignment.context),
checks its statements and result using [sequence and result typing](#claim-assignment.completion),
and must satisfy the [completion obligation](destructors.md#claim-destructors.finished_environment):
only empty or struct locals remain. This condition uses current descriptions,
so an empty class slot is permitted while an initialized partial class is not.

[Class drops](destructors.md#claim-destructors.drop_typing) use whole given
receivers and the dedicated destructor name; struct drops give and discard
without invoking user code.
```

```{definition} assignment.declaration_typing
:lean: Assignment/Typing:DeclarationsTyped
:uses: assignment.syntax assignment.body_typing

A *well-typed declaration table* has distinct callable names. Each declaration
has a signature obeying the [ordinary call restrictions](functions.md#claim-functions.signatures)
and [destructor restrictions](destructors.md#claim-destructors.declarations),
and a [well-typed body](#claim-assignment.body_typing) checked against the entire
table. Signatures are therefore available recursively; there is no termination
requirement.
```

```{definition} assignment.program_typing
:lean: Assignment/Typing:ProgramTyped
:uses: assignment.declaration_typing assignment.completion assignment.body_typing assignment.context

A *well-typed program* has a
[well-formed class table](shared-typing.md#claim-shared.typing.well_formed_classes)
and a [well-typed declaration table](#claim-assignment.declaration_typing).
Its main sequence [checks](#claim-assignment.completion) from the empty
[context](#claim-assignment.context) and satisfies the same
[completion obligation](#claim-assignment.body_typing) as a function body.
```

## Appendix: store and stack safety

```{theorem} assignment.write_ownership
:lean: Assignment/WriteOwnership:Write.preserves_pending
:uses: assignment.write shared.well_formed

Suppose the input state is [structurally well formed](shared.md#claim-shared.well_formed),
counting the incoming reference and any other
[pending references](shared.md#claim-shared.pending_live) as roots.
A [write to a writable slot](#claim-assignment.write) preserves that invariant
when the incoming reference leaves the pending roots and the displaced reference,
if any, joins them instead.

This is an ownership exchange before collection. The displaced reference remains
a temporary root even when no local or field reaches it after the write.
The theorem assumes neither allocation-age order nor global acyclicity.
```

```{theorem} assignment.store_safety
:lean: Assignment/StoreSoundness:store_sound
:uses: assignment.store assignment.write shared.typing.realization

Suppose the [static store operation](#claim-assignment.store) succeeds and the
input state [realizes](shared-typing.md#claim-shared.typing.realization) its current
environment, with the incoming value and any other pending values as roots.
A [writable, replaceable runtime destination and write](#claim-assignment.write)
then exist.

For every such runtime write, the resulting state realizes the output current
environment and all the original pending values except the installed incoming
value. Any additional pending values needed to retain displaced storage have
[struct types](shared.md#claim-shared.struct), so they can be discarded by the
statement's [collector](#claim-assignment.machine). For a field destination,
the output type uses [view replacement](#claim-assignment.view); incoming
negative entries still describe empty fields.
```

```{definition} assignment.stack_typing
:lean: Assignment/StackTyping:BodyFrom Assignment/StackTyping:ContinuationTyped Assignment/StackTyping:StackShape Assignment/StackTyping:ConfigurationTyped
:uses: assignment.completion assignment.body_typing assignment.declaration_typing assignment.context assignment.machine functions.frame_slots shared.typing.realization

A *typed configuration* has [well-formed nominal declarations](shared-typing.md#claim-shared.typing.well_formed_classes),
[typed callable declarations](#claim-assignment.declaration_typing), and a compatible
[stack](#claim-assignment.machine). Each frame's locals form a
[typed store](functions.md#claim-functions.frame_slots) for the current descriptions
in its [context](#claim-assignment.context).

The active body's remainder checks from that context. A suspended caller's
remainder checks from the context after [result delivery](#claim-assignment.completion).
Every body satisfies the [completion obligation](#claim-assignment.body_typing).
The empty stack has no result destination and no roots.

The common heap has [Shared realization](shared-typing.md#claim-shared.typing.realization)
with an empty local environment and all frame references as pending values.
Their multiplicities and types are retained, so equal shared references in two
slots still contribute two roots. Frame-local names need not be globally unique.
```

```{theorem} assignment.progress
:lean: Assignment/Safety:ConfigurationTyped.progress
:uses: assignment.stack_typing assignment.machine

Every [typed configuration](#claim-assignment.stack_typing) has no remaining
frames—that is, it is [finished](#claim-assignment.finished)—or can take a
[machine step](#claim-assignment.machine). This covers
stores, calls, returns, explicit drops, and the initial-frame exit.
```

```{theorem} assignment.preservation
:lean: Assignment/Safety:ConfigurationTyped.preservation
:uses: assignment.stack_typing assignment.machine

Every [machine step](#claim-assignment.machine) from a
[typed configuration](#claim-assignment.stack_typing) produces another typed
configuration. The result quantifies over every operational successor and
includes eager collection after the raw transition.
```

```{definition} assignment.retains_classes
:lean: Assignment/Safety:RetainsClasses
:uses: assignment.machine shared.struct

A [collection](#claim-assignment.machine) *retains classes* when every object whose nominal type is not a
[struct](shared.md#claim-shared.struct) remains present with the same identity
and contents. The comparison uses the heap immediately before collection and
the heap after it.
```

```{theorem} assignment.collection_safety
:lean: Assignment/Safety:RawStep.sound
:uses: assignment.stack_typing assignment.retains_classes assignment.machine

For every [raw transition](#claim-assignment.machine) from a
[typed configuration](#claim-assignment.stack_typing), collection produces a
typed configuration and [retains every class object](#claim-assignment.retains_classes)
still present after that transition. An
[explicit unpack](shared-typing.md#claim-shared.typing.bindings) can remove a class
container during the raw transition; collection cannot consume it on the
program's behalf.

Overwriting a struct reference can discard its entire unreachable subgraph.
Since [struct fields have struct types](shared.md#claim-shared.struct), this
cannot hide an unconsumed class, including behind a view omission.
```

```{theorem} assignment.ownership
:lean: Assignment/Safety:ConfigurationTyped.ownership
:uses: assignment.stack_typing shared.well_formed

In a [typed configuration](#claim-assignment.stack_typing), references in all
frame slots and object fields are [pairwise compatible](shared.md#claim-shared.well_formed).
Distinct owning occurrences can target the same object only when both are
shared. Every referenced object is allocated, and every allocated object has
an incoming reference from a frame or field.
```

```{theorem} assignment.empty_completion
:lean: Assignment/Safety:ConfigurationTyped.finished_heap_empty
:uses: assignment.stack_typing assignment.machine

A [typed configuration](#claim-assignment.stack_typing) with
[no frames](#claim-assignment.finished) has an empty heap. No class or struct
objects remain after completion.
```

```{theorem} assignment.safety
:lean: Assignment/Safety:program_safety
:uses: assignment.program_typing assignment.stack_typing assignment.machine assignment.execution assignment.finished assignment.stuck

Starting from a [well-typed program](#claim-assignment.program_typing), every finite
[execution](#claim-assignment.execution) ends in a
[typed configuration](#claim-assignment.stack_typing). It is
[finished](#claim-assignment.finished) or can take another
[machine step](#claim-assignment.machine), and is not
[stuck](#claim-assignment.stuck). This includes stores within recursive
functions and destructors; the theorem makes no termination claim.
```
