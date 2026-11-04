# Destructors

## Every owned class value needs an ending

````{example} destructors.example.consume
:lean: Destructors/ChapterChecks:consumption

Before a body finishes, it must account for every class value it owns. [Unpacking](shared-typing.md#claim-shared.typing.bindings)
consumes a container and transfers responsibility for its fields to local
bindings. Dropping delegates that work to the class's destructor. [Moving a
value](shared.md#claim-shared.give) to another local merely transfers the responsibility.

Start with classes that have no destructors:

```dada
class Token {}
class Pair { left: Token, right: Token }

let pair = new Pair(new Token(), new Token());
let Pair → { left, right } = pair→;
let Token → {} = left→;
let Token → {} = right→;
```

This program checks: unpacking consumes the pair, then each token.
If either of the last two statements is omitted, the body cannot finish. The
corresponding token is still owned by a local binding. Unpacking the outer
container alone does not consume the contents. Since these classes have no
destructors, replacing an unpack with `drop` is not permitted.

Likewise, ending the body with `let other = right→;` instead of unpacking
`right` would leave `other` responsible for that token. The obligation follows
the value. [Struct values](shared.md#claim-shared.declarations) are exempt from this requirement; their storage is
treated as garbage collected.
````

## Delegating consumption to a destructor

````{example} destructors.example.wrapper
:lean: Destructors/ExecutionChecks:wrapper_consumed

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

The execution moves `w` into the wrapper destructor's `self` binding.
[Unpacking](shared-typing.md#claim-shared.typing.bindings) consumes the wrapper container and transfers its field to `resource`.
Dropping that field invokes the resource destructor, whose unpack consumes the
resource container. Both destructor calls then finish, and `w` has been emptied by the drop before the initial program frame exits. Nothing implicitly destroys the receiver or its fields.

This chapter introduces the new behavior first. The explicit forward
references to the [inherited machinery in the appendix](#claim-destructors.inherited)
keep Shared's unchanged rules from obscuring that behavior. The appendix states
which rules carry over and supplies their definitions in Shared.
````

## Parameters and locals in a function

````{example} destructors.function_example
:lean: Destructors/ChapterChecks:function_bodies
:uses: destructors.example.wrapper destructors.example.consume functions.typing

Using the preceding [Functions chapter](functions.md), these examples add the
[consumption requirement](#claim-destructors.example.consume) to ordinary function bodies. They use the `Wrapper`
and `Resource` [declarations above](#claim-destructors.example.wrapper). Both an
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
A function can also transfer ownership to its caller by [returning a value](functions.md#claim-functions.return);
check its remaining locals after evaluating that return expression.
````

## Declarations and dropping

```{definition} destructors.declarations
:lean: Destructors/Syntax:Name Destructors/Syntax:Signature.WellFormed Destructors/Syntax:Declaration Destructors/Syntax:Statement Destructors/Syntax:Statement.dropClass Destructors/Syntax:Body Destructors/Syntax:Program
:uses: shared.declarations shared.struct

A declaration retains [Shared's name, kind, and ordered fields](shared.md#claim-shared.declarations). A `class`
declaration may additionally contain one destructor, written `drop { body }`,
where `body` is a sequence of statements. The destructor has no parameters or
result; its initial local binding is `self`, a [uniquely owned whole instance](shared-typing.md#claim-shared.typing.types)
of the declaring class. A `struct` or `shared struct` has no destructor body
in this layer.

The core distinguishes ordinary function names, qualified method names, and
`drop(C)` destructor names. A destructor is stored as a declaration with exactly
one parameter `→self` of its owning class and no result. Names must be unique;
ordinary methods cannot collide with destructor names.

Classes without destructors remain legal. Their instances must be consumed
through [explicit unpacking](shared-typing.md#claim-shared.typing.bindings), possibly after being moved to another owner.
[Struct fields still have only struct types](shared.md#claim-shared.struct), and classes still cannot be shared.
The inherited declaration restrictions are collected in the
[appendix](#claim-destructors.inherited).
```

```{definition} destructors.droppable
:lean: Destructors/Typing:Droppable
:uses: destructors.declarations shared.typing.types shared.struct

The *droppability judgment* `Droppable(T)` says that an explicit drop can consume a value of
type `T`, using a well-formed declaration table. Types retain [Shared's permissions and signed views](shared-typing.md#claim-shared.typing.types), summarized in the
[appendix](#claim-destructors.inherited).

| Type of value | Condition for `Droppable(T)` |
| --- | --- |
| Struct, including shared struct | Any well-formed permission and view allowed for that nominal type. |
| Class | Given permission, a whole declared view, and a [declared destructor](#claim-destructors.declarations). |

“Whole” means that [view normalization](shared-typing.md#claim-shared.typing.normalization) exposes the entire declared value, not
merely every currently visible field. A partially moved class cannot invoke its
destructor. An omitted field is [unknown](given-typing.md#claim-given.typing.views), not evidence that the field is empty.
```

```{definition} destructors.drop_typing
:lean: Destructors/Typing:DropTyped Destructors/Typing:StatementTyped
:uses: destructors.droppable shared.typing.giving

The new statement is `drop p`, where `p` is a [place](shared.md#claim-shared.syntax) (a local followed by zero or
more field names). An [environment](shared-typing.md#claim-shared.typing.environments) `Γ` maps local names to types or empty slots.
Write `Give(Γ, p) = (T, Γ′)` for [Shared's static ordinary-give operation](shared-typing.md#claim-shared.typing.giving),
recalled in the [appendix](#claim-destructors.inherited).

The surface statement elaborates to a struct-discard operation or to
`drop(C)(p→)`, a core call to the [destructor name](#claim-destructors.declarations)
with no destination. The class name comes from the given value's type. This
elaboration inserts no implicit drops and adds no receiver-call sugar.

The rule is:

- Compute `Give(Γ, p) = (T, Γ′)`.
- [Require `Droppable(T)`](#claim-destructors.droppable).
- Check the following statements under `Γ′`.

For a class this moves the value out of its source and calls its destructor.
For a struct, dropping the resulting value invokes no code and destroys no
object. Struct storage is treated as if garbage collected.

For structs, use exactly the ordinary-give effect.
A given struct moves out, leaving an empty slot; a shared struct reference is
copied, leaving its source initialized. The empty local binding is retained,
as for ordinary give. No binding is removed.
```

## Finishing a frame

```{definition} destructors.finished_environment
:lean: Destructors/Typing:Finished Destructors/Step:StoreFinished
:uses: shared.struct destructors.drop_typing

An environment is *finished* when each binding is either empty or has a [struct
type](shared.md#claim-shared.struct). A class binding is an outstanding obligation even if its class has a
destructor, its view is partial, or all of its fields are empty. A frame may
finish only when its statement sequence is exhausted and its environment is
finished.

A *[frame](functions.md#claim-functions.machine)* owns a local environment and a sequence of statements still to run.
There is one program frame and one fresh frame per active function, method,
or destructor call.
Names are local to their frame; a destructor cannot access its caller's locals.

Moving a class to another local transfers the obligation. Storing it inside a
class transfers the obligation to that owner; [unpacking](shared-typing.md#claim-shared.typing.bindings) transfers obligations
to the resulting field bindings. No class can be hidden inside a struct,
because struct fields must themselves have struct types.

Frame completion discards remaining struct bindings without running code.
It inserts no drops and performs no implicit unpacking.
```

```{definition} destructors.body_typing
:lean: Destructors/Typing:BodyTyped Destructors/Typing:DeclarationsTyped Destructors/Typing:ProgramTyped
:uses: destructors.declarations destructors.finished_environment destructors.drop_typing

Check every [declared destructor body](#claim-destructors.declarations) starting with exactly `self: given C`,
where `C` is its declaring class with its whole view. Its statements must type
check and leave a [finished environment](#claim-destructors.finished_environment). Check ordinary functions and methods using their declared parameters and
result types from the [Functions signatures](functions.md#claim-functions.signatures),
requiring a finished environment after evaluation of any return expression.
Check the top-level program from the empty environment with the same final
condition.

All declared destructor signatures are available while checking each body.
A call checks [droppability](#claim-destructors.droppable), not an inline expansion of the called body. The
whole declaration table is accepted only when every declared body checks.
This permits recursive destructor calls, including `drop self`.

The inherited rules for declarations, expressions, fresh bindings, and
unpacking otherwise apply; the [appendix](#claim-destructors.inherited)
identifies those rules. Assignment is not part of this layer.
```

````{example} destructors.example.boundaries
:lean: Destructors/ChapterChecks:boundaries
:uses: destructors.body_typing destructors.droppable

These [checks](#claim-destructors.body_typing) distinguish a declared destructor from explicit cleanup:

```dada
class Resource {
    drop { }
}
```

This alternative destructor fails: the body leaves `self` initialized. Even a fieldless
class must unpack its receiver or transfer it to another consuming operation.

```dada
class Again {
    drop { drop self; }
}
```

This declaration checks, but dropping an `Again` instance recurses forever.
Each call moves its receiver into the next frame; none returns.

A class [without a destructor cannot be explicitly dropped](#claim-destructors.droppable), but it can be
unpacked. After moving a field out of a class that does have a destructor,
dropping the remaining partial instance is also rejected. Explicit unpacking
can consume that container when the [inherited unpacking rule](shared-typing.md#claim-shared.typing.bindings) knows the status
of every direct field; its resulting class bindings still require consumption.
````

## Calling and returning

```{definition} destructors.machine
:lean: Destructors/Step:Frame Destructors/Step:Configuration Destructors/Step:Configuration.initial Destructors/Step:Configuration.rootState Destructors/Step:Configuration.collect Destructors/Step:Configuration.finished
:uses: destructors.finished_environment shared.state functions.machine functions.gc

A configuration contains a common heap, the allocation counter, an active
frame, and a stack of suspended caller frames, including result destinations for
ordinary calls as in [Functions](functions.md#claim-functions.machine). This
layer strengthens [Functions' frame-exit rule](functions.md#claim-functions.execution): a returning body must discharge
its [class obligations](#claim-destructors.finished_environment), and remaining struct bindings may be discarded. [Eager
GC](functions.md#claim-functions.gc) still runs after each transition, including popping the initial frame.
A runtime frame contains its
local store and remaining statements. A local store maps names to empty slots
or references. Heap objects, references, and allocation follow the
[Shared representation](shared.md#claim-shared.state); object modes still
belong to references.

The caller stack is empty initially. The initial active frame contains the
program and an empty local store. Caller frames retain their locals while a
destructor runs, but those locals are inaccessible to the callee. Roots used
by the heap invariant include references in every frame, not just the active
one, together with temporary values during expression evaluation.
```

```{definition} destructors.execution
:lean: Destructors/Step:RawStep Destructors/Step:Step
:uses: destructors.machine destructors.drop_typing destructors.body_typing shared.give

The transition rules extend [Functions' ordinary call and return
machinery](functions.md#claim-functions.execution) with destructor calls and [stricter completion](#claim-destructors.finished_environment):

| Transition | Action |
| --- | --- |
| Inherited statement | Execute a Shared binding or [unpacking statement](shared-typing.md#claim-shared.typing.steps) in the active frame and common heap, then advance that frame. |
| Drop struct | Perform [ordinary give](shared.md#claim-shared.give) from the source place, discard the resulting struct reference, and advance the active frame. No destructor runs; [eager GC](functions.md#claim-functions.gc) reclaims the object if it is no longer reachable. |
| Call class destructor | Perform ordinary give as the sole argument to the [declared destructor](#claim-destructors.declarations), suspend the updated caller with its following statements, and start the destructor body in a fresh frame containing only `self` bound to that reference. |
| Return | Evaluate any ordinary function or method result as in Functions, require no initialized class locals remain, discard the remaining struct locals, and resume the caller with its result if any. A destructor returns no value. |
| Finish program | When the program frame has no statements and no initialized class locals, discard its remaining locals and enter a terminal configuration. |

The call transfers the reference directly to `self`; it does not destroy the
object. Return does not delete a receiver object. Explicit unpacking is what
removes a class container. A destructor's statements may allocate, unpack, or
call another destructor using the same rules as the program.

The destructor signature requires a uniquely owned whole instance: all declared
fields and their declared subtrees are present, with the permissions required by
their types. This is checked statically, using the same argument typing as
ordinary calls; the machine does not repeat the view check at runtime. An exhausted
frame with an initialized class local cannot return or finish; typing must
exclude such configurations.
```

## Safety and relation to Shared

```{definition} destructors.heap_obligations
:lean: Destructors/StackTyping:BodyFrom Destructors/StackTyping:ContinuationTyped Destructors/StackTyping:StackShape Destructors/StackTyping:ConfigurationTyped Destructors/Safety:RetainsClasses
:uses: destructors.machine destructors.execution shared.well_formed shared.liveness

A typed configuration has a well-formed declaration table, a compatible typing
of all [live frames](#claim-destructors.machine), and a common heap realizing all
of their roots. Its frame typing checks each active body from its current local
environment. For a suspended caller it checks the remainder from the environment
after result delivery. Every body ends in a [finished environment](#claim-destructors.finished_environment).

The heap realization is [Shared's realization](shared-typing.md#claim-shared.typing.realization)
with an empty variable environment and the frame roots as pending values. Roots
retain their multiplicity and their types; frame-local names need not be globally
unique. Nominal field correctness covers fields hidden by views.

Write `RetainsClasses(H, H′)` when every non-struct object present in heap `H`
is still present, unchanged, in heap `H′`. This is the collection obligation:
GC may reclaim structs, but a class must be consumed explicitly.

The ownership condition still excludes [simultaneous unique and shared paths](shared.md#claim-shared.path_exclusivity)
to an object. Class references remain unique, and struct objects cannot contain
class references. After the initial frame is popped, collection leaves the
terminal heap empty. An explicit unpack removes its class container;
a destructor call alone does not discharge that object's obligation.

Hiding a field in a [view](shared-typing.md#claim-shared.typing.types) does not erase a runtime class obligation.
```

```{theorem} destructors.collection_safety
:lean: Destructors/Safety:RawStep.sound
:uses: destructors.heap_obligations destructors.execution

For every [raw transition](#claim-destructors.execution) from a
[typed configuration](#claim-destructors.heap_obligations), collection produces
another typed configuration and retains every class object still present after
the raw transition. Explicit unpacking may remove a class container during the
raw transition; collection cannot remove it on the program's behalf.

The proof discards only struct roots. Since [struct fields have struct types](shared.md#claim-shared.struct),
those roots cannot be the sole routes to class objects, even when their views
omit fields.
```

```{theorem} destructors.empty_completion
:lean: Destructors/Safety:ConfigurationTyped.finished_heap_empty
:uses: destructors.heap_obligations destructors.machine

A [typed configuration](#claim-destructors.heap_obligations) with [no frames](#claim-destructors.machine) has
an empty heap. There are no remaining class or struct objects.
```

```{theorem} destructors.safety
:lean: Destructors/Safety:program_safety
:uses: destructors.heap_obligations destructors.body_typing destructors.execution

Starting from a [well-typed program](#claim-destructors.body_typing), every finite
execution prefix ends in a [typed configuration](#claim-destructors.heap_obligations).
That configuration is terminal or can [take a step](#claim-destructors.execution),
and is not stuck. Recursive functions and destructors are allowed; this theorem
does not assert termination.
```

```{theorem} destructors.shared_boundary
:lean: Correspondence/FunctionsDestructors:step_correspondence
:uses: destructors.body_typing destructors.execution shared.typing.safety

Embed a Functions program by preserving its classes, ordinary names, signatures,
local statements, and calls. Map each body and frame componentwise. The embedded
fragment has no destructor declarations or drop statements.

Require an *exit condition*: if the current body has no statements, every possible
[result evaluation](functions.md#claim-functions.return) must leave a store whose
initialized locals are structs, as required by [frame completion](#claim-destructors.finished_environment).
This condition is vacuous while a local statement or call remains.

Under this condition, a step from an embedded Functions configuration exists
exactly when it is the embedding of a Functions step, including its collection.
The backward implication quantifies over arbitrary destructor-machine successors.
Thus local operations and ordinary calls retain their behavior. Frame exit adds
the explicit consumption requirement.

The typing boundary is intentionally stronger. A Functions or Shared program
may discard an initialized class local at exit; this layer rejects it. Preservation
of all earlier program typings and completions is therefore not claimed.
```

## Deferred conveniences

```{future-note} destructors.future

Assignment comes after this layer. Inserting explicit drops at scope exits and
around control flow is a later desugaring step, rather than behavior supplied
implicitly by these rules.

The spelling `self → { resource }` could eventually abbreviate
`let Wrapper → { resource } = self→;`, with the nominal type inferred.
This layer uses the [explicit pattern](shared-typing.md#claim-shared.typing.patterns).

After borrows are introduced, reconsider whether structs should support a
user-defined drop body receiving a shared borrow of `self`. This is a tentative
idea, not part of the destructor layer.
```

## Appendix: inherited Shared machinery

```{definition} destructors.inherited
:lean: Destructors/Syntax:Parameter Destructors/Syntax:Signature Destructors/Typing:ResultTyped Destructors/Typing:DestinationTyped Destructors/Typing:SequenceTyped
:uses: shared.declarations shared.struct shared.syntax shared.state shared.give shared.typing.types shared.typing.giving shared.typing.expressions shared.typing.patterns shared.typing.statements

The preceding rules use the following Shared machinery unchanged, except for
imposing the [completion condition](#claim-destructors.finished_environment) defined above; frames already exist in Shared.
These links identify the full inherited definitions; this summary fixes their
role in this layer.

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
storage at each transition boundary. Class obligations survive until explicit consumption.
```
