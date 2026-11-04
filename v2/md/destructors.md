# Destructors

## Every owned class value needs an ending

````{future-note} destructors.example.consume

This chapter records a proposed extension, not part of the formalized language.
All examples, rules, and safety statements below are nonnormative design notes
for review before implementation.

Before a body finishes, it must account for every class value it owns. Unpacking
consumes a container and transfers responsibility for its fields to local
bindings. Dropping delegates that work to the class's destructor. Moving a
value to another local merely transfers the responsibility.

Start with classes that have no destructors:

```dada
class Token {}
class Pair { left: Token, right: Token }

let pair = new Pair(new Token(), new Token());
let Pair → { left, right } = pair→;
let Token → {} = left→;
let Token → {} = right→;
```

This proposed program checks: unpacking consumes the pair, then each token.
If either of the last two statements is omitted, the body cannot finish. The
corresponding token is still owned by a local binding. Unpacking the outer
container alone does not consume the contents. Since these classes have no
destructors, replacing an unpack with `drop` is not permitted.

Likewise, ending the body with `let other = right→;` instead of unpacking
`right` would leave `other` responsible for that token. The obligation follows
the value. Struct values are exempt from this requirement; their storage is
treated as garbage collected.
````

## Delegating consumption to a destructor

````{future-note} destructors.example.wrapper

A destructor lets a class say how to finish using an instance. This layer makes
that work explicit: a class value must be moved, unpacked, or dropped before its
frame finishes. Declaring a destructor does not arrange an automatic call.

```dada
class Resource {
    drop {
        let Resource → {} = self→;
    }
}
class Wrapper {
    resource: Resource
    drop {
        let Wrapper → { resource } = self→;
        drop resource;
    }
}

let w = new Wrapper(new Resource());
drop w;
```

The proposed execution moves `w` into the wrapper destructor's `self` binding.
Unpacking consumes the wrapper container and transfers its field to `resource`.
Dropping that field invokes the resource destructor, whose unpack consumes the
resource container. Both destructor calls then finish, and the program finishes
with `w` empty. Nothing implicitly destroys the receiver or its fields.

This chapter is a rule sketch; its definitions and examples await Lean
formalization. It introduces the new behavior first. The explicit forward
references to the [inherited machinery in the appendix](#appendix-inherited-shared-machinery)
keep Shared's unchanged rules from obscuring that behavior. The appendix states
which rules carry over and supplies their definitions in Shared.
````

## Parameters and locals in a function

````{future-note} destructors.function_example
:uses: destructors.example.wrapper destructors.example.consume functions.typing

Using the preceding [Functions chapter](functions.md), these examples add the
consumption requirement to ordinary function bodies. They use the `Wrapper`
and `Resource` declarations above. Both an
owned parameter and a locally created class value must be accounted for before
the function returns.

One version explicitly unpacks everything:

```dada
fn finish(w: → Wrapper) {
    let extra = new Resource();
    let Wrapper → { resource } = w→;
    let Resource → {} = resource→;
    let Resource → {} = extra→;
}
```

Another delegates the work to destructors:

```dada
fn finish(w: → Wrapper) {
    let extra = new Resource();
    drop w;
    drop extra;
}
```

These are alternative bodies. In either version, omitting the consumption of
`extra` would leave an owned class value at return. Merely having a destructor
would not make that omission legal in this explicit core. Likewise, unpacking
`w` and leaving `resource` unconsumed would fail to account for its contents.

The requirement applies to program, function, method, and destructor bodies.
A function can also transfer ownership to its caller by returning a value;
check its remaining locals after evaluating that return expression.
````

## Declarations and dropping

```{future-note} destructors.declarations
:uses: shared.declarations shared.struct

A declaration retains Shared's name, kind, and ordered fields. A `class`
declaration may additionally contain one destructor, written `drop { body }`,
where `body` is a sequence of statements. The destructor has no parameters or
result; its initial local binding is `self`, a uniquely owned whole instance
of the declaring class. A `struct` or `shared struct` has no destructor body
in this layer.

Classes without destructors remain legal. Their instances must be consumed
through explicit unpacking, possibly after being moved to another owner.
Struct fields still have only struct types, and classes still cannot be shared.
The inherited declaration restrictions are collected in the
[appendix](#claim-destructors.inherited).
```

```{future-note} destructors.droppable
:uses: destructors.declarations shared.typing.types shared.struct

The judgment `Droppable(T)` says that an explicit drop can consume a value of
type `T`. Types retain Shared's permissions and signed views, summarized in the
[appendix](#claim-destructors.inherited).

| Type of value | Condition for `Droppable(T)` |
| --- | --- |
| Struct, including shared struct | Any well-formed permission and view allowed for that nominal type. |
| Class | Given permission, a whole declared view, and a declared destructor. |

“Whole” means that view normalization exposes the entire declared value, not
merely every currently visible field. A partially moved class cannot invoke its
destructor. An omitted field is unknown, not evidence that the field is empty.
```

```{future-note} destructors.drop_typing
:uses: destructors.droppable shared.typing.giving

The new statement is `drop p`, where `p` is a place (a local followed by zero or
more field names). An environment `Γ` maps local names to types or empty slots.
Write `Give(Γ, p) = (T, Γ′)` for Shared's static ordinary-give operation,
recalled in the [appendix](#claim-destructors.inherited).

The proposed rule is:

- Compute `Give(Γ, p) = (T, Γ′)`.
- Require `Droppable(T)`.
- Check the following statements under `Γ′`.

For a class this moves the value out of its source and calls its destructor.
For a struct, dropping the resulting value invokes no code and destroys no
object. Struct storage is treated as if garbage collected.

**Provisional source effect for structs:** use exactly the ordinary-give effect.
A given struct moves out, leaving an empty slot; a shared struct reference is
copied, leaving its source initialized. The empty local binding is retained,
as for ordinary give. This choice is part of the sketch to review; the agreed
no-destruction behavior does not by itself decide the source-slot behavior.
```

## Finishing a frame

```{future-note} destructors.finished_environment
:uses: shared.struct destructors.drop_typing

A *frame* owns a local environment and a sequence of statements still to run.
There is one program frame and one fresh frame per active function, method,
or destructor call.
Names are local to their frame; a destructor cannot access its caller's locals.

An environment is *finished* when each binding is either empty or has a struct
type. A class binding is an outstanding obligation even if its class has a
destructor, its view is partial, or all of its fields are empty. A frame may
finish only when its statement sequence is exhausted and its environment is
finished.

Moving a class to another local transfers the obligation. Storing it inside a
class transfers the obligation to that owner; unpacking transfers obligations
to the resulting field bindings. No class can be hidden inside a struct,
because struct fields must themselves have struct types.

Frame completion discards remaining struct bindings without running code.
It inserts no drops and performs no implicit unpacking.
```

```{future-note} destructors.body_typing
:uses: destructors.declarations destructors.finished_environment destructors.drop_typing

Check every declared destructor body starting with exactly `self: given C`,
where `C` is its declaring class with its whole view. Its statements must type
check and leave a finished environment. Check ordinary functions and methods using their declared parameters and
result types from the [Functions layer](functions.md#claim-functions.typing),
requiring a finished environment after evaluation of any return expression.
Check the top-level program from the empty environment with the same final
condition.

All declared destructor signatures are available while checking each body.
A call checks droppability, not an inline expansion of the called body. The
whole declaration table is accepted only when every declared body checks.
This permits recursive destructor calls, including `drop self`.

The inherited rules for declarations, expressions, fresh bindings, and
unpacking otherwise apply; the [appendix](#claim-destructors.inherited)
identifies those rules. Assignment is not part of this layer.
```

````{future-note} destructors.example.boundaries
:uses: destructors.body_typing destructors.droppable

These proposed checks distinguish a declared destructor from explicit cleanup:

```dada
class Empty {
    drop { }
}
```

This declaration fails: the body leaves `self` initialized. Even a fieldless
class must unpack its receiver or transfer it to another consuming operation.

```dada
class Again {
    drop { drop self; }
}
```

This declaration checks, but dropping an `Again` instance recurses forever.
Each call moves its receiver into the next frame; none returns.

A class without a destructor cannot be explicitly dropped, but it can be
unpacked. After moving a field out of a class that does have a destructor,
dropping the remaining partial instance is also rejected. Explicit unpacking
can consume that container when the inherited unpacking rule knows the status
of every direct field; its resulting class bindings still require consumption.
````

## Calling and returning

```{future-note} destructors.machine
:uses: destructors.finished_environment shared.state functions.machine functions.gc

A configuration contains a common heap, the allocation counter, an active
frame, and a stack of suspended caller frames, including result destinations for
ordinary calls as in [Functions](functions.md#claim-functions.machine). This
layer strengthens Functions' frame-exit rule: a returning body must discharge
its class obligations, and remaining struct bindings may be discarded. Eager
GC still runs after each transition, including popping the initial frame.
A runtime frame contains its
local store and remaining statements. A local store maps names to empty slots
or references. Heap objects, references, and allocation follow the
[inherited representation](#claim-destructors.inherited); object modes still
belong to references.

The caller stack is empty initially. The initial active frame contains the
program and an empty local store. Caller frames retain their locals while a
destructor runs, but those locals are inaccessible to the callee. Roots used
by the heap invariant include references in every frame, not just the active
one, together with temporary values during expression evaluation.
```

```{future-note} destructors.execution
:uses: destructors.machine destructors.drop_typing destructors.body_typing shared.give

The proposed transition rules extend Functions' ordinary call and return
machinery with destructor calls and stricter completion:

| Transition | Action |
| --- | --- |
| Inherited statement | Execute a Shared binding or unpacking statement in the active frame and common heap, then advance that frame. |
| Drop struct | Perform ordinary give from the source place, discard the resulting struct reference, and advance the active frame. No destructor runs; eager GC reclaims the object if it is no longer reachable. |
| Call class destructor | Perform ordinary give, require a unique whole instance with a declared destructor, suspend the updated caller with its following statements, and start the destructor body in a fresh frame containing only `self` bound to that reference. |
| Return | Evaluate any ordinary function or method result as in Functions, require no initialized class locals remain, discard the remaining struct locals, and resume the caller with its result if any. A destructor returns no value. |
| Finish program | When the program frame has no statements and no initialized class locals, discard its remaining locals and enter a terminal configuration. |

The call transfers the reference directly to `self`; it does not destroy the
object. Return does not delete a receiver object. Explicit unpacking is what
removes a class container. A destructor's statements may allocate, unpack, or
call another destructor using the same rules as the program.

“Whole instance” in the call transition means all declared fields and their
declared subtrees are present, with the permissions required by their types.
The type system establishes this requirement before execution. An exhausted
frame with an initialized class local cannot return or finish; typing must
exclude such configurations.
```

## Safety and relation to Shared

```{future-note} destructors.heap_obligations
:uses: destructors.machine destructors.execution shared.well_formed shared.liveness

The proposed heap invariant retains Shared's structural and kind restrictions
with roots drawn from all live frames. Before collection, every remaining
class object must be reachable from a frame or temporary evaluation value;
class obligations cannot be discharged by making an object unreachable.
Struct objects may become unreachable during a raw transition. Eager GC
removes them before the next machine configuration.

The ownership condition still excludes simultaneous unique and shared paths
to an object. Class references remain unique, and struct objects cannot contain
class references. After the initial frame is popped, collection leaves the
terminal heap empty. An explicit unpack removes its class container;
a destructor call alone does not discharge that object's obligation.

The exact realization relation connecting signed views, all stack frames,
and temporary roots remains to be formalized. In particular, hiding a field
in a view must not erase a runtime class obligation.
```

```{future-note} destructors.safety
:uses: destructors.heap_obligations destructors.body_typing destructors.execution

Target safety statement: starting from a well-typed program and a well-typed
declaration table, every reachable configuration satisfies the heap invariant
and has a compatible typing of its frames. Each such configuration is terminal
or can take a step. Every step preserves these properties. Terminal
configurations contain no class objects.

This target allows infinite execution. There is no completion bound in terms
of the number of source statements: destructor calls can recurse indefinitely.
These are proof obligations for the next implementation step, not established
results of this sketch.
```

```{future-note} destructors.shared_boundary
:uses: destructors.body_typing destructors.execution shared.typing.safety

The intended correspondence with Shared preserves and reflects execution of
its binding and unpacking statements in a single frame, up to the new frame
completion check. Expressions, ordinary give, allocation, and unpacking retain
their previous behavior.

Ordinary function and method calls retain the preceding Functions behavior
except at frame exit: bodies must now satisfy the consumption condition before
the frame is popped and collection runs. Thus Functions programs also need a separate
completion-condition qualification when relating the two layers.

The new typing boundary is intentionally stronger. A Shared program may finish
with a class local still initialized; the same program is rejected here.
Consequently, preservation of all Shared program typings and completions is
not a proposed extension theorem. The correspondence should isolate unchanged
statement behavior and state separately the extra consumption condition needed
for program completion.
```

## Deferred conveniences

```{future-note} destructors.future

Assignment comes after this layer. Inserting explicit drops at scope exits and
around control flow is a later desugaring step, rather than behavior supplied
implicitly by these rules.

The spelling `self → { resource }` could eventually abbreviate
`let Wrapper → { resource } = self→;`, with the nominal type inferred.
The initial sketch uses the explicit pattern.

After borrows are introduced, reconsider whether structs should support a
user-defined drop body receiving a shared borrow of `self`. This is a tentative
idea, not part of the proposed destructor layer.
```

## Appendix: inherited Shared machinery

```{future-note} destructors.inherited
:uses: shared.declarations shared.struct shared.syntax shared.state shared.give shared.typing.types shared.typing.giving shared.typing.expressions shared.typing.patterns shared.typing.statements

The preceding rules use the following Shared machinery unchanged, except for
imposing the completion condition defined above; frames already exist in Shared.
These links identify the full inherited definitions; this summary fixes their
role in the sketch.

| Machinery | Inherited meaning |
| --- | --- |
| [Declarations and kinds](shared.md#claim-shared.declarations) | Nominal names and ordered named fields; classes, structs, and shared structs. Only structs satisfy [struct(T)](shared.md#claim-shared.struct); struct fields have struct types. |
| [Syntax](shared.md#claim-shared.syntax) | Places start at locals and follow named fields. Expressions give a place, give-share a place, or construct an object from ordered argument expressions. Bindings use fresh local names. |
| [Storage](shared.md#claim-shared.state) | References carry modes and object identifiers. Object fields contain references or empty slots. Allocation uses fresh, monotonically allocated identifiers. |
| [Types and views](shared-typing.md#claim-shared.typing.types) | Given and shared permissions, whole declared types, and signed views. Positive entries expose whole subtrees, negative entries record empty slots, and omissions are unknown. |
| [Ordinary give](shared.md#claim-shared.give) | Move through a unique path, emptying its final slot; copy through shared access, promoting a unique final reference if necessary. [Static give](shared-typing.md#claim-shared.typing.giving) computes the result type and source environment. |
| [Construction](shared-typing.md#claim-shared.typing.expressions) | Evaluate arguments left to right; require whole declared argument types. Shared structs construct shared references immediately. |
| [Unpacking](shared-typing.md#claim-shared.typing.patterns) | A unique result can be unpacked with `C → { fields }`, removing the container and transferring its field slots to bindings. Every direct field's status must be known; transferred objects may themselves be partial. Shared references cannot be unpacked. |

Shared's completion bound of one step per statement plus initial-frame exit
does not carry over.
Rootedness now counts all live frames; eager GC removes unreachable struct
storage at each transition boundary. The new safety targets above additionally
require that class obligations survive until explicit consumption.
```
