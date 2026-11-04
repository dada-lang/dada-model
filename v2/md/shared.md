# Shared: operational semantics

```{definition} shared.references
:lean: Shared/Syntax:ObjectId Shared/State:Mode Shared/State:Reference Shared/State:Reference.owned Shared/State:Reference.shared Shared/State:Slot
:uses: given.identities

Shared ownership lets several references own the same object. A *reference*
\\(r\\) pairs a *mode* \\(\kappa\\) with an object identity \\(\alpha\\).
The object itself has no ownership mode. Variables and object fields are slots;
their *contents* \\(s\\) are empty or hold one reference:

\\[
\begin{aligned}
\kappa &::= \mathsf{unique}\mid\mathsf{shared} \\
r &::= (\kappa,\alpha) \\
s &::= \bot\mid r.
\end{aligned}
\\]

Object identities are [tagged natural numbers](given.md#claim-given.identities),
written \\(\mathsf{obj}(n)\\), with \\(\operatorname{index}(\mathsf{obj}(n))=n\\).
```

```{definition} shared.give
:lean: Shared/Syntax:Place Shared/Step:Resolve Shared/Step:Take Shared/Step:Promote Shared/Step:Give
:uses: shared.references given.syntax

A [place expression](given.md#claim-given.syntax) \\(p\\) follows fields from a variable to select a slot. Giving it, `p→`,
requires every slot and intermediate object on the route to exist, and every
slot to hold a reference. It moves the reference when every [reference](#claim-shared.references) along
that route is unique. If any is shared, it returns a shared copy and keeps the
source initialized:

| Path access | Stored mode | Result mode | Source slot afterwards |
| --- | --- | --- | --- |
| Unique | Unique | Unique | Empty |
| Shared | Shared | Shared | Unchanged |
| Shared | Unique | Shared | Stored reference becomes shared |

In every case, the result refers to the source reference's object. When copying
a unique reference through shared access, the stored reference becomes shared
too. Only the reference in that final slot changes; every other reference and
object identity stay unchanged.

Sharing a container leaves its field references' modes alone. Those fields are
already reached through a shared path, even if their own references are unique.
Copying one of those references later makes the final stored reference shared
as well.
```


```{definition} shared.declarations
:lean: Shared/Syntax:Kind Shared/Syntax:Class Shared/State:Kind.mode

A nominal type has a name and an ordered list of fields. Its declaration chooses
whether its values can be shared and whether construction makes them shared
immediately:

| Declaration | May be shared | Constructor result |
| --- | --- | --- |
| `class C { ... }` | No | Given `C` |
| `struct C { ... }` | Yes | Given `C` |
| `shared struct C { ... }` | Yes | `shared C` |

These three forms describe nominal types; they do not introduce three different
kinds of runtime object representation. [Modes](#claim-shared.references) still belong to references.
```



```{definition} shared.struct
:lean: Shared/Syntax:Kind.isStruct Shared/TypingViews:StructType Shared/TypingViews:ClassTable.WellFormed Shared/TypingViews:KindValid
:uses: shared.declarations

The predicate `struct(T)` means that the nominal type underlying `T` is [declared](#claim-shared.declarations)
as either `struct` or `shared struct`. It does not depend on the reference's
current permission or on which fields its [view exposes](given-typing.md#claim-given.typing.views). It is false for a class.

Every field of a struct, including a shared struct, must itself have a struct
type. This restriction applies to all declared fields, including ones hidden by
a view or currently empty. Classes may contain either classes or structs.
Thus sharing a container cannot expose a class through shared field access.
A `shared C` type is permitted only when `struct(C)` holds.

This layer checks `struct(T)` directly from nominal declarations. Generic type
parameters, user-written predicates, and predicate where-clauses are not part of
this language. Destructors and assignment belong to later layers.
```



````{example} shared.example.declarations
:lean: Shared/KindChecks:declarations
:uses: shared.declarations shared.struct

These declarations distinguish the [three forms](#claim-shared.declarations) without requiring primitive types:

```dada
struct Token {}
struct Box { value: Token }
shared struct SharedBox { value: Token }
class Resource { token: Token }
class Owner { resource: Resource, box: Box }
```

`Box` and `SharedBox` satisfy the [struct-only field restriction](#claim-shared.struct). `Owner` may
contain a `Resource` because `Owner` is a class. In contrast, both of the
following declarations are rejected:

```dada
struct BadBox { resource: Resource }
shared struct BadSharedBox { resource: Resource }
```

An empty view of `Resource` would not make either declaration valid: hiding its
fields does not make the nominal type a struct.
````


## Places, values, and programs

```{definition} shared.classes
:lean: Shared/Syntax:ClassName Shared/Syntax:FieldName Shared/Syntax:Class
:uses: shared.references

A *nominal declaration* named \\(C\\), in \\(\mathsf{ClassName}\\), declares an ordered
list of \\(n\\) fields, where \\(n\\) is a natural number including zero.
A *field name* \\(f\\) belongs to \\(\mathsf{FieldName}\\). Constructor
arguments supply the fields in order. Source fields have types checked by the
type system. The operational declaration retains its [kind](#claim-shared.declarations)
and ordered field names; all values are objects.
```

```{definition} shared.syntax
:lean: Shared/Syntax:VariableId Shared/Syntax:Place Shared/Syntax:Value Shared/Syntax:Statement
:uses: shared.classes shared.give given.syntax

A *variable name* \\(x\\) belongs to \\(\mathsf{VariableId}\\). A [place
expression](given.md#claim-given.syntax) \\(p\\) starts at a variable and follows fields. A *value
expression* \\(e\\) gives from a place, gives and shares the result, or
constructs an object. A *statement* \\(t\\) binds an expression's result:

\\[
\begin{aligned}
p &::= x\mid p.f \\
e &::= p\mathord{\to} \\
  &\phantom{{}::={}}\mid p\mathord{\to}\mathsf{share} \\
  &\phantom{{}::={}}\mid\mathsf{new}\ C(e_1,\ldots,e_n) \\
t &::= \mathsf{let}\ x=e
\end{aligned}
\\]

The expression `p→share` performs the [give](#claim-shared.give), requires a
[struct](#claim-shared.struct) result, then makes that result a shared owner.
A class result cannot be shared.
Giving along a unique route empties the source. To share a newly constructed
object, first construct it in a variable, then give-share that variable.

Each `let` names a fresh runtime variable. Constructor arguments are
value expressions, evaluated from left to right; they may themselves construct objects.
There is no shadowing, scope, call, assignment, destruction, or borrowing in this
fragment.
```

```{definition} shared.programs
:lean: Shared/Syntax:Classes Shared/Syntax:Program
:uses: shared.classes shared.syntax given.programs given.collections

A *program* \\(\Pi=\langle\Delta,P\rangle\\) has a *class table* \\(\Delta\\)
and a finite ordered sequence \\(P\\) of [statements](#claim-shared.syntax):

\\[
\begin{aligned}
\Delta &\in \mathsf{ClassName}\rightharpoonup(\mathsf{Kind}\times\mathsf{List}(\mathsf{FieldName})),\\
P &::= []\mid t::P.
\end{aligned}
\\]

The [finite-map and list notation](given.md#claim-given.collections) is unchanged.
For a [nominal declaration](#claim-shared.classes) of [kind](#claim-shared.declarations) \\(k\\) listing \\(f_1,\ldots,f_n\\),
\\(\Delta(C)=(k,[f_1,\ldots,f_n])\\).
```

```{definition} shared.well_formed_classes
:lean: Shared/Soundness:ClassesWellFormed
:uses: shared.programs

A [class table](#claim-shared.programs) is *well formed* when class names
are distinct and each declaration lists distinct field names.
```

## Copying a field

````{example} shared.example.copy_field
:lean: Shared/Examples:sharing_execution
:uses: shared.syntax shared.give

Start with no objects or variables and execute:

```dada
struct Token {}
struct Box { value: Token }

let t = new Token();
let b = new Box(t→);
let s = b→share;
let u = s.value→;
let v = s.value→;
```

The first two statements construct a token and put its reference in a box,
leaving `t` empty. The third moves the box's reference out of `b` and makes it
shared in `s`. The box's field still holds a unique reference to the token.

The fourth statement reaches the token through [shared variable](#claim-shared.give) `s`. It changes
the reference in the box's `value` field to shared and gives `u` a shared copy.
The fifth copies the already-shared reference into `v`.

After these statements, before frame exit, there are still two objects.
Variable `s` is a shared owner of the
box. The box's field, `u`, and `v` are three [shared owners](#claim-shared.references) of the token. Variables
`t` and `b` are empty. Both field gives succeed because neither empties the field.
````

## Objects and slots

```{definition} shared.objects
:lean: Shared/State:Object
:uses: shared.classes shared.references

An *object* \\(o\\) has a [class name](#claim-shared.classes) and named
field slots, whose [contents](#claim-shared.references) can be empty:

\\[
o::=C\{f_1:s_1,\ldots,f_n:s_n\}.
\\]
```

```{definition} shared.state
:lean: Shared/State:State
:uses: shared.references shared.objects shared.programs given.collections

A *storage state* \\(S=\langle O,V,\nu\rangle\\) consists of the object table,
variable table, and allocation counter \\(\nu\\). Object identities are [tagged numbers](#claim-shared.references).
Creation uses \\(\mathsf{obj}(\nu)\\), then increments the counter.

We use [finite-map notation](given.md#claim-given.collections) for tables with distinct keys:

\\[
O\in\mathsf{ObjectId}\rightharpoonup\mathsf{Object},\qquad
V\in\mathsf{VariableId}\rightharpoonup\mathsf{Slot},\qquad
\nu\in\mathbb N.
\\]
```

```{definition} shared.empty_state
:lean: Shared/State:State.empty
:uses: shared.state

The *empty storage state* has no objects or variables, and counter zero:

\\[S_{\emptyset}=\langle\varnothing,\varnothing,0\rangle.\\]

Here \\(\varnothing\\) denotes the empty map.
```

```{definition} shared.storage_places
:lean: Shared/State:StoragePlace
:uses: shared.syntax shared.references

A *storage place* \\(q\\) selects one slot directly: a variable or a field
of a particular object:

\\[
q::=x\mid\alpha.f.
\\]

A [place expression](#claim-shared.syntax) follows a route to a slot; a storage
place identifies the slot itself.
```

```{definition} shared.lookup
:lean: Shared/State:Stored
:uses: shared.state shared.storage_places shared.references

*Slot lookup* \\(S[q]=s\\) reads the contents at a
[storage place](#claim-shared.storage_places). For
[storage](#claim-shared.state) \\(S=\langle O,V,\nu\rangle\\):

\\[
\begin{aligned}
S[x]&=V(x)&&\text{when }V(x)\text{ is defined},\\
S[\alpha.f_i]&=s_i&&\text{when }O(\alpha)=C\{f_1:s_1,\ldots,f_n:s_n\},\ 1\le i\le n.
\end{aligned}
\\]

An empty slot still exists; lookup at an absent variable, object, or field is
undefined. A [reference](#claim-shared.references) identifies an object in
\\(O\\); the slot does not contain that object's data.
```

## Reading a route

```{definition} shared.mode_join
:lean: Shared/State:Mode.join
:uses: shared.references

*Mode combination* \\(\kappa_0\sqcup\kappa_1\\) combines the access to a
containing object with the [mode](#claim-shared.references) of a field's reference.
The result is unique only when both are unique:

\\[
\kappa_0\sqcup\kappa_1 =
\begin{cases}
\mathsf{unique} & \kappa_0=\mathsf{unique}\ \land\ \kappa_1=\mathsf{unique},\\
\mathsf{shared} & \text{otherwise}.
\end{cases}
\\]
```

```{definition} shared.resolution
:lean: Shared/Step:Resolve
:uses: shared.lookup shared.syntax shared.mode_join shared.storage_places

Resolving a [place](#claim-shared.syntax) reads its route without changing the state. Write
\\(S\vdash p\Downarrow q:\alpha@\kappa\\) when the route selects a [storage place](#claim-shared.storage_places)
\\(q\\) and object \\(\alpha\\), with effective access mode \\(\kappa\\).
The effective mode describes the entire route, not just the last stored reference.

A variable starts with its stored reference's mode. A field combines the mode
of its prefix with its own using [mode combination](#claim-shared.mode_join):

\\[
\frac{\href{#claim-shared.lookup}{S[x]}=(\kappa,\alpha)}
{S\vdash x\Downarrow x:\alpha@\kappa}
\qquad
\frac{S\vdash p\Downarrow q:\beta@\kappa_0\quad
\href{#claim-shared.lookup}{S[\beta.f]}=(\kappa_1,\alpha)}
{S\vdash p.f\Downarrow\beta.f:\alpha@\href{#claim-shared.mode_join}{(\kappa_0\sqcup\kappa_1)}}.
\\]

Thus once a shared reference occurs along a path, the rest of that path has
shared access. An [absent variable](#claim-shared.lookup), a missing field or intermediate object, or
an empty slot prevents resolution.
```

## Executing statements

```{definition} shared.machine
:lean: Shared/Frames:Frame Shared/Frames:Configuration Shared/Frames:Configuration.running Shared/Frames:Configuration.initial Shared/Frames:Configuration.state
:uses: shared.state shared.syntax

A *frame* \\(f=(V,P)\\) owns its local variable store \\(V\\) and remaining
[statements](#claim-shared.syntax) \\(P\\). The [program](#claim-shared.programs) has one initial frame; after its exit there is
no frame. Heap objects \\(O\\) and the allocation counter \\(\nu\\) live outside it:

\\[
K=\langle O,\nu,F\rangle,\qquad F::=\mathsf{none}\mid\mathsf{some}(V,P).
\\]

For expression evaluation, combine the live frame's locals with the heap and
counter as the [storage](#claim-shared.state) \\(S=\langle O,V,\nu\rangle\\). Write
\\(\operatorname{run}(S,P)=\langle O,\nu,\mathsf{some}(V,P)\rangle\\).
The pair \\(\langle S,P\rangle\\) used by local statement rules is an
observation of that live frame, not a terminal program state.

Initially \\(K=\operatorname{run}(S_{\emptyset},P)\\), including when \\(P=[]\\).
Exhausting the statements leaves a live frame whose bindings can still be
inspected. A separate exit step pops it. There are no nested scopes or calls in
this layer; Functions will extend this single-frame lifetime to a stack.
```


```{definition} shared.gc
:lean: Shared/State:Live Shared/Frames:State.collect Shared/Frames:Configuration.collect
:uses: shared.machine shared.state

*Reachability* starts at an initialized slot of the [live frame](#claim-shared.machine) and follows
[initialized object fields](#claim-shared.objects). Write \\(\mathsf{Live}_S(\alpha)\\) when this reaches
object \\(\alpha\\). An absent frame has no roots.

*Eager collection* retains exactly reachable object entries. For object data
\\(D\\) (its class tag and field slots), define:

\\[
\operatorname{gc}(K)=\langle
 [(\alpha,D)\in O\mid\mathsf{Live}_{S_K}(\alpha)],\nu,F\rangle.
\\]

Here \\(S_K\\) uses the frame's locals, or an empty variable store if the
frame is absent. Collection preserves surviving objects and their identifiers,
the allocation counter, and the frame. It invokes no user code. With no frame,
it removes the entire heap.

The Lean definition is a mathematical reachability filter, not an executable
traversal. Collection runs after whole statements and frame exit, never between
constructor operands or while an expression result awaits binding.
```


```{definition} shared.finished
:lean: Shared/Frames:Configuration.finished
:uses: shared.machine

A [configuration](#claim-shared.machine) is *finished* exactly when its initial
frame has been popped:

\\[
\mathsf{Finished}(\langle O,\nu,F\rangle)\iff F=\mathsf{none}.
\\]

An empty statement sequence still has a live frame and can take its exit step.
Completion discards the frame's locals and collects its unreachable objects.
```
```{definition} shared.evaluation
:lean: Shared/Step:Eval Shared/Step:EvalArgs Shared/Step:State.allocate Shared/Step:StructReference Shared/Step:StructArguments Shared/State:Kind.mode
:uses: shared.give shared.references shared.state shared.programs shared.struct shared.declarations

*Expression evaluation*, written

\\[
\Delta\vdash\langle S,e\rangle\Downarrow\langle S',r\rangle,
\\]

produces a [reference](#claim-shared.references) and updated
[storage](#claim-shared.state). These clauses define successful evaluation:

- **Give.** Evaluate `p→` by [giving from its route](#claim-shared.give).
  The result is unique when it moves and shared when it copies.
- **Give-share.** Evaluate `p→share` by the same give, require that its result targets a [struct](#claim-shared.struct), then replace the result's
  mode with shared, preserving its object identity. This last conversion changes
  no stored slot.
- **Construct.** Evaluate arguments from left to right, then create an object
  containing their results in declaration order:

\\[
\frac{
\begin{gathered}
\href{#claim-shared.programs}{\Delta(C)}=(k,[f_1,\ldots,f_n])\\
\Delta\vdash\langle S_{i-1},e_i\rangle\Downarrow\langle S_i,r_i\rangle
\quad(1\le i\le n)\\
\beta\notin\operatorname{dom}(O_n)\\
\mathsf{isStruct}(k)\Rightarrow\forall i.\;\mathsf{StructReference}_{\Delta,S_n}(r_i)
\end{gathered}
}{
\Delta\vdash\langle S_0,\mathsf{new}\ C(e_1,\ldots,e_n)\rangle
\Downarrow\langle S',(\mathsf{mode}(k),\beta)\rangle
}
\quad\text{Construct}
\\]

where

\\[
\begin{aligned}
S_n&=\langle O_n,V_n,\nu_n\rangle,\\
\beta&=\href{#claim-shared.references}{\mathsf{obj}(\nu_n)},\\
O'&=O_n[\beta\mapsto C\{f_1:r_1,\ldots,f_n:r_n\}],\\
S'&=\langle O',V_n,\nu_n+1\rangle.
\end{aligned}
\\]

Here `mode(k)` is shared for a shared struct and unique otherwise, as specified
by the [declaration kinds](#claim-shared.declarations). `StructReference` means
that the reference targets an allocated object whose declaration is a struct.
The argument guard applies to both struct kinds and prevents constructing a
struct containing a class even in an untyped program.

Here \\(S_i\\) is the storage after the first \\(i\\) arguments;
\\(\operatorname{dom}(O_n)\\) is its set of allocated identities and the map update
adds the fresh object's entry. An empty class takes no arguments and uses
\\(S_n=S_0\\). Argument results remain owned by the evaluation until placed in
the new object's fields. An unknown class, wrong argument count, or failed
argument evaluation gives no successful construction.
```

```{definition} shared.steps
:lean: Shared/Step:State.bind Shared/Step:Step Shared/Frames:Step Shared/Frames:baseOperation Shared/Frames:patternOperation
:uses: shared.machine shared.evaluation shared.gc shared.finished

An auxiliary *local statement operation* \\(\Delta\vdash K\rightsquigarrow K'\\) executes the first
statement in a local observation of the [frame](#claim-shared.machine). It completes
[expression evaluation](#claim-shared.evaluation), stores the result in a fresh
variable, and removes the statement:

\\[
\frac{
\href{#claim-shared.evaluation}{\Delta\vdash\langle S,e\rangle\Downarrow\langle S',r\rangle}
\quad x\notin\operatorname{dom}(V')
}{
\Delta\vdash\langle S,(\mathsf{let}\ x=e)::P\rangle
\rightsquigarrow\langle\langle O',V'[x\mapsto r],\nu'\rangle,P\rangle
}
\quad\text{Let}
\\]

where \\(S'=\langle O',V',\nu'\rangle\\), and \\(V'[x\mapsto r]\\) adds
variable \\(x\\) holding \\(r\\). The remaining statements keep their order.
If evaluation fails or the variable already exists, there is no transition.
All argument evaluations belong to this one step; there is no separately
observable state partway through a failed expression.
Write \\(\rightsquigarrow\\) for that local
operation. The program machine collects after it and has a separate exit rule:

\\[
\frac{\Delta\vdash\langle S,P\rangle\rightsquigarrow\langle S',P'\rangle}
 {\Delta\vdash\operatorname{run}(S,P)\longrightarrow
   \operatorname{gc}(\operatorname{run}(S',P'))}
\qquad
\Delta\vdash\operatorname{run}(\langle O,V,\nu\rangle,[])
 \longrightarrow\operatorname{gc}(\langle O,\nu,\mathsf{none}\rangle).
\\]

The exit target has no frame and an empty heap, retaining counter \\(\nu\\).
Even an empty program takes one exit step. A finished [configuration](#claim-shared.machine) has no
successor. The Lean `Step` in `Shared/Step` is the auxiliary local relation;
`Framed.Step` is this program machine. `baseOperation` selects the single-variable
binding relation; later `patternOperation` selects the unpacking relation.

```
````{example} shared.example.frame_lifetime
:lean: Shared/FrameChecks:lifetime
:uses: shared.machine shared.steps shared.gc

```dada
class Token {}
let t = new Token();
```

The first [step](#claim-shared.steps) binds the token in the [initial frame](#claim-shared.machine). That frame is still live
even though its statements are exhausted. The second step pops it and [collects](#claim-shared.gc)
the token, leaving an empty heap and allocation counter one. An empty program
has no statements but still takes its initial-frame exit step.
````



````{example} shared.example.immediately_shared
:lean: Shared/KindChecks:immediately_shared
:uses: shared.example.declarations shared.steps shared.give

Using the [declarations above](#claim-shared.example.declarations):

```dada
let b = new SharedBox(new Token());
let c = b→;
let t = b.value→;
```

Construction gives `b` a [shared reference immediately](#claim-shared.declarations). Giving `b` copies that
reference into `c`, leaving `b` initialized. The token field initially holds a
unique reference; giving it through shared `b` [promotes](#claim-shared.give) that stored reference
and produces a shared token in `t`. Immediate sharing of the container does not
require its fields to have been stored with shared modes.

````



````{example} shared.example.class_boundary
:lean: Shared/KindChecks:class_boundary
:uses: shared.example.declarations shared.steps shared.give

`new Resource(new Token())` produces a unique [class reference](#claim-shared.declarations).
Binding it to `r` and then evaluating `r→share` is [rejected](#claim-shared.struct). Plain `r→` remains
a [move](#claim-shared.give); a class may contain structs without becoming shareable itself.
````


```{definition} shared.executions
:lean: Shared/Frames:Steps Shared/Frames:StepsExactly
:uses: shared.steps

A *finite execution* \\(\Delta\vdash K\longrightarrow^{*}K'\\) consists
of zero or more [statement steps](#claim-shared.steps):

\\[
\frac{}{\Delta\vdash K\longrightarrow^{*}K}
\qquad
\frac{\href{#claim-shared.steps}{\Delta\vdash K\longrightarrow K'}
\quad\Delta\vdash K'\longrightarrow^{*}K''}
{\Delta\vdash K\longrightarrow^{*}K''}.
\\]
```

```{definition} shared.stuck
:lean: Shared/Frames:Stuck
:uses: shared.steps shared.finished shared.give

A configuration is *stuck* when its frame remains but no
[step](#claim-shared.steps) is available:

\\[
\mathsf{Stuck}_{\Delta}(K)\iff
\neg\href{#claim-shared.finished}{\mathsf{Finished}(K)}\ \land\
\neg\exists K'.\;\href{#claim-shared.steps}{\Delta\vdash K\longrightarrow K'}.
\\]

For example, [giving](#claim-shared.give) through an entirely unique path empties
its slot, so giving it again cannot evaluate and leaves the machine stuck.
Repeated gives through shared access leave the source initialized.
```

## A shared link inside a path

````{example} shared.example.share_value
:lean: Shared/Examples:share_value
:uses: shared.state shared.syntax shared.give shared.steps

Use `struct Token {}` and `struct Box { value: Token }`. Let object \\(\mathsf{obj}(0)\\) be a token and
object \\(\mathsf{obj}(1)\\) a box, with these slots and allocation counter \\(2\\):

| Slot | Contents |
| --- | --- |
| `b` | Unique owner of box \\(\mathsf{obj}(1)\\) |
| `t` | Empty |
| Box \\(\mathsf{obj}(1)\\), field `value` | Unique owner of token \\(\mathsf{obj}(0)\\) |

Execute:

```dada
let s = b→share;
```

Variable `s` receives a [shared owner](#claim-shared.references) of box \\(\mathsf{obj}(1)\\), and `b` becomes empty.
The field remains a unique owner of token \\(\mathsf{obj}(0)\\). The objects, empty `t`,
and allocation counter are unchanged.
````

````{example} shared.example.shared_middle
:lean: Shared/Examples:nested_shared_path
:uses: shared.example.share_value shared.resolution shared.give shared.steps

Start again from the pre-exit storage of {anchor-ref}`shared.example.share_value`,
before copying its field. Execute:

```dada
class Outer { value: shared Box }
let outer = new Outer(s→);
let u = outer.value.value→;
```

The [constructor](#claim-shared.evaluation) copies shared variable `s` into the new outer object \\(\mathsf{obj}(2)\\); `s`
remains initialized. Variable `outer` uniquely owns the outer object \\(\mathsf{obj}(2)\\). The give
then traverses three references: unique `outer`, shared `outer.value` to box
\\(\mathsf{obj}(1)\\), and the unique `value` field of box \\(\mathsf{obj}(1)\\) to token \\(\mathsf{obj}(0)\\).

The shared middle link makes this a shared access even though the first and
last stored references are unique. The give changes only the reference in box
\\(\mathsf{obj}(1)\\)'s `value` field to shared, and `u` receives a shared owner of token \\(\mathsf{obj}(0)\\). `outer`
stays unique; its field stays shared; `s` still refers to box \\(\mathsf{obj}(1)\\).
All three objects remain allocated and the allocation counter is \\(3\\).
````

## Liveness and well-formedness

```{definition} shared.allocated
:lean: Shared/State:Allocated
:uses: shared.state

An object is *allocated* when its identity appears in the
[object table](#claim-shared.state):

\\[
\mathsf{Allocated}_S(\alpha)\iff\alpha\in\operatorname{dom}(O).
\\]
```

```{definition} shared.live
:lean: Shared/State:Live
:uses: shared.lookup shared.references

An object is *live* when an owning path reaches it from a variable,
following occupied slots. Both unique and shared
[references](#claim-shared.references) contribute owning edges:

\\[
\frac{\href{#claim-shared.lookup}{S[x]}=(\kappa,\alpha)}{\mathsf{Live}_S(\alpha)}
\qquad
\frac{\mathsf{Live}_S(\beta)\quad\href{#claim-shared.lookup}{S[\beta.f]}=(\kappa,\alpha)}
{\mathsf{Live}_S(\alpha)}.
\\]

Empty slots contribute no edge.
```

```{definition} shared.well_formed
:lean: Shared/State:Allocated Shared/State:Live Shared/State:References Shared/Soundness:Owners Shared/Soundness:Compatible Shared/Soundness:WellFormed Shared/Soundness:WellFormedWith Shared/KindSafety:HasKind Shared/KindSafety:ReferenceAllowed Shared/KindSafety:KindCorrect Shared/KindSafety:WellFormedState
:uses: shared.state

[Allocated objects](#claim-shared.allocated) and [live objects](#claim-shared.live)
are distinguished by presence in storage and reachability from roots.

A [state](#claim-shared.state) is well formed, written \\(\mathsf{WF}_{\Delta}(S)\\), when:

- Object identities and variable names are each distinct.
- Every object's class is [declared](#claim-shared.programs), and its distinct field names match the
  declaration's order, including fields whose slots are empty.
- Every [allocated identity](#claim-shared.allocated) has an index below the allocation counter. Field
  references target objects with strictly smaller indices.
- Every stored reference targets an allocated object, and every allocated
  object has at least one stored owning reference.
- Any two distinct owning occurrences targeting the same object are both shared.
- Every occupied field of a struct targets another struct object.
- Every shared reference targets a struct, and every reference to an instance
  of a shared struct is shared.

The first five clauses are *structural well-formedness*. The final two are the
declaration-kind invariants. Structural well-formedness also has a form that
counts pending expression results as additional owning occurrences; this lets
expression soundness describe values not yet placed in a slot.

Owning occurrences are counted across all variable slots and all object fields.
The ownership-compatibility condition permits several shared references to an
object, but a stored unique reference must be its only incoming owning reference. That local condition
does not by itself give a path unique access: every preceding reference must
also be unique. The older-object condition follows construction order and prevents
an owner-only cycle with no variable root.
```

```{theorem} shared.path_exclusivity
:lean: Shared/KindSafety:WellFormedState.path_mode_exclusive
:uses: shared.well_formed shared.resolution

In a [well-formed state](#claim-shared.well_formed), no object can be reached both by an entirely unique
path and by a path containing a shared reference:

\\[
\begin{aligned}
&\mathsf{WF}_{\Delta}(S)\;\land\;
  (\href{#claim-shared.resolution}{S\vdash p\Downarrow q:\alpha@\mathsf{unique}})\\
&\quad\Longrightarrow\quad
  \neg\exists p',q'.\ \href{#claim-shared.resolution}{S\vdash p'\Downarrow q':\alpha@\mathsf{shared}}.
\end{aligned}
\\]

The paths start at variables. A unique reference stored inside a shared
container does not contradict this property: the path through that container
already contains a shared reference.
```

```{theorem} shared.liveness
:lean: Shared/KindSafety:WellFormedState.live_iff_allocated
:uses: shared.well_formed

In a [well-formed state](#claim-shared.well_formed), an object is live exactly when it is allocated:

\\[
\mathsf{WF}_{\Delta}(S)
\quad\Longrightarrow\quad
\bigl(\href{#claim-shared.live}{\mathsf{Live}_S(\alpha)}\iff\href{#claim-shared.allocated}{\mathsf{Allocated}_S(\alpha)}\bigr).
\\]

Every allocated object therefore has an owning path from a variable. Sharing
allows several such paths without making missing objects reachable.
```


```{theorem} shared.gc_inert
:lean: Shared/Frames:State.collect_eq_self
:uses: shared.gc shared.well_formed shared.liveness

[Collection](#claim-shared.gc) leaves [structurally well-formed evaluation storage](#claim-shared.well_formed) unchanged:
every allocated object is already [reachable](#claim-shared.live). Ordinary statements preserve
this property, so their following collection is inert. Popping the frame
removes its roots; collection at that boundary empties the heap instead.
```


```{theorem} shared.soundness
:lean: Shared/FrameInvariants:base_soundness
:uses: shared.state shared.syntax shared.give shared.steps shared.well_formed shared.liveness shared.path_exclusivity

For any program with a [well-formed class table](#claim-shared.well_formed_classes), every configuration reached by
a [finite execution](#claim-shared.executions) from the [empty initial state](#claim-shared.machine) has a [well-formed state](#claim-shared.well_formed). This
includes intermediate configurations and the state after the final statement.

Consequently, every allocated object remains [live](#claim-shared.liveness). In each such state, a unique
stored reference is the only incoming owner of its object; when an object has
several incoming owners, all those references are shared. [No object has both
a unique path and a shared path](#claim-shared.path_exclusivity) from variables. This covers both explicit
[give-share](#claim-shared.evaluation) and [copying](#claim-shared.give) through a shared path, including the change to the path's
final stored reference.
```

## The Given fragment inside Shared

```{definition} shared.embedding
:lean: Correspondence/UniqueSharedFrames:embed Correspondence/UniqueShared:embedId Correspondence/UniqueShared:embedReference Correspondence/UniqueShared:embedSlots Correspondence/UniqueShared:embedObject Correspondence/UniqueShared:embedState Correspondence/UniqueShared:embedPlace Correspondence/UniqueShared:embedValue Correspondence/UniqueShared:embedStatement Correspondence/UniqueShared:embedClasses Correspondence/UniqueShared:embedProgram Correspondence/UniqueShared:embedConfiguration
:uses: given.classes given.state given.syntax given.unpacking shared.state shared.syntax

The Shared language contains a translation of the [Given fragment with
single-variable bindings](given.md#claim-given.syntax). This section restricts the correspondence to that
fragment. Write
\\(E\\) for this translation, applied to programs, configurations, and their
components.

For a [state](given.md#claim-given.state), \\(E\\) replaces every [reference](#claim-shared.references) \\(\alpha\\) with the unique
reference \\((\mathsf{unique},\alpha)\\). Empty slots remain empty. Class names,
field names, variable names, object identities, table order, and the next-identity
counter are preserved.

For a [program](given.md#claim-given.programs), \\(E\\) preserves its class declarations, places, constructors,
gives, and statement order. Every Given declaration becomes a `class`, never a
`struct` or `shared struct`. It introduces no give-share expression. For a
[configuration](given.md#claim-given.machine), it translates the heap and any live frame, preserving the counter
and the distinction between a live frame and no frame. Thus a
related pair describes the same point in the same computation, with explicit
unique mode tags in the Shared state.
```

```{theorem} shared.correspondence
:lean: Correspondence/UniqueSharedFrames:base_step_correspondence
:uses: given.steps shared.steps shared.embedding

For every class table \\(\Delta\\) and configuration \\(c\\) of this Given
fragment, the [embedding](#claim-shared.embedding) matches steps in both directions:

- If \\(\href{given.html#claim-given.steps}{\Delta\vdash c\longrightarrow c'}\\), then
  \\(\href{#claim-shared.steps}{E(\Delta)\vdash E(c)\longrightarrow E(c')}\\).
- If \\(\href{#claim-shared.steps}{E(\Delta)\vdash E(c)\longrightarrow d}\\), then there is a Given
  successor \\(c'\\) with \\(\href{given.html#claim-given.steps}{\Delta\vdash c\longrightarrow c'}\\) and
  \\(d=E(c')\\).

The second statement covers every Shared successor \\(d\\); it does not
assume in advance that \\(d\\) is a translated state. These statements give
a one-step bisimulation between Given and its embedded fragment: Shared adds
no behavior to translated Given computations, and loses none of their steps.
```

```{theorem} shared.boundaries
:lean: Correspondence/UniqueSharedFrames:base_boundary_correspondence
:uses: given.syntax given.steps shared.syntax shared.steps shared.embedding shared.correspondence

For every program in the Given fragment with single-variable bindings,
[translating](#claim-shared.embedding) its [initial configuration](given.md#claim-given.machine) gives exactly the [initial configuration](#claim-shared.machine)
of its translated Shared program.

For every configuration in this fragment, the translated configuration is [finished](#claim-shared.finished) exactly
when the original is [finished](given.md#claim-given.finished). Using the program's class table, the translated
configuration is [stuck](#claim-shared.stuck) exactly when the original is [stuck](given.md#claim-given.stuck). The correspondence
therefore agrees on how execution starts, on successful completion, and on the
absence of an available step before completion.
```
