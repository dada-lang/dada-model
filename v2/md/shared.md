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

## Places, values, and programs

```{definition} shared.classes
:lean: Shared/Syntax:ClassName Shared/Syntax:FieldName Shared/Syntax:Class
:uses: shared.references

A *class* named \\(C\\), in \\(\mathsf{ClassName}\\), declares an ordered
list of \\(n\\) fields, where \\(n\\) is a natural number including zero.
A *field name* \\(f\\) belongs to \\(\mathsf{FieldName}\\). Constructor
arguments supply the fields in order. Fields have no declared types; all values
are objects.
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

The expression `p→share` performs the [give](#claim-shared.give), then makes its result a shared owner.
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
\Delta &\in \mathsf{ClassName}\rightharpoonup\mathsf{List}(\mathsf{FieldName}),\\
P &::= []\mid t::P.
\end{aligned}
\\]

The [finite-map and list notation](given.md#claim-given.collections) is unchanged.
For a [class declaration](#claim-shared.classes) listing \\(f_1,\ldots,f_n\\),
\\(\Delta(C)=[f_1,\ldots,f_n]\\).
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

The [give rules](#claim-shared.give) distinguish moving from copying.
Start with no objects or variables and execute:

```dada
class Token {}
class Box { value }

let t = new Token();
let b = new Box(t→);
let s = b→share;
let u = s.value→;
let v = s.value→;
```

The first two statements construct a token and put its reference in a box,
leaving `t` empty. The third moves the box's reference out of `b` and makes it
shared in `s`. The box's field still holds a unique reference to the token.

The fourth statement reaches the token through shared variable `s`. It changes
the reference in the box's `value` field to shared and gives `u` a shared copy.
The fifth copies the already-shared reference into `v`.

At the end, there are still two objects. Variable `s` is a shared owner of the
box. The box's field, `u`, and `v` are three shared owners of the token. Variables
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
:lean: Shared/State:Configuration Shared/State:Configuration.initial
:uses: shared.state shared.programs shared.empty_state

A *configuration* \\(K=\langle S,P\rangle\\) pairs
[storage](#claim-shared.state) with its remaining
[statement sequence](#claim-shared.programs). Execution of a program
\\(\Pi=\langle\Delta,P\rangle\\) starts at \\(\langle S_{\emptyset},P\rangle\\),
where \\(S_{\emptyset}\\) is the [empty storage](#claim-shared.empty_state).
The class table \\(\Delta\\) remains fixed.
```

```{definition} shared.finished
:lean: Shared/State:Configuration.finished
:uses: shared.machine

A [configuration](#claim-shared.machine) is *finished* exactly when its
statement sequence is empty:

\\[
\mathsf{Finished}(\langle S,P\rangle)\iff P=[].
\\]

Final variables and objects remain in storage.
```

```{definition} shared.evaluation
:lean: Shared/Step:Eval Shared/Step:EvalArgs Shared/Step:State.allocate
:uses: shared.give shared.references shared.state shared.programs

*Expression evaluation*, written

\\[
\Delta\vdash\langle S,e\rangle\Downarrow\langle S',r\rangle,
\\]

produces a [reference](#claim-shared.references) and updated
[storage](#claim-shared.state). These clauses define successful evaluation:

- **Give.** Evaluate `p→` by [giving from its route](#claim-shared.give).
  The result is unique when it moves and shared when it copies.
- **Give-share.** Evaluate `p→share` by the same give, then replace the result's
  mode with shared, preserving its object identity. This last conversion changes
  no stored slot.
- **Construct.** Evaluate arguments from left to right, then create an object
  containing their results in declaration order:

\\[
\frac{
\begin{gathered}
\href{#claim-shared.programs}{\Delta(C)}=[f_1,\ldots,f_n]\\
\Delta\vdash\langle S_{i-1},e_i\rangle\Downarrow\langle S_i,r_i\rangle
\quad(1\le i\le n)\\
\beta\notin\operatorname{dom}(O_n)
\end{gathered}
}{
\Delta\vdash\langle S_0,\mathsf{new}\ C(e_1,\ldots,e_n)\rangle
\Downarrow\langle S',(\mathsf{unique},\beta)\rangle
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

Here \\(S_i\\) is the storage after the first \\(i\\) arguments;
\\(\operatorname{dom}(O_n)\\) is its set of allocated identities and the map update
adds the fresh object's entry. An empty class takes no arguments and uses
\\(S_n=S_0\\). Argument results remain owned by the evaluation until placed in
the new object's fields. An unknown class, wrong argument count, or failed
argument evaluation gives no successful construction.
```

```{definition} shared.steps
:lean: Shared/Step:State.bind Shared/Step:Step
:uses: shared.machine shared.evaluation

A *statement step* \\(\Delta\vdash K\longrightarrow K'\\) executes the first
statement in a [configuration](#claim-shared.machine). It completes
[expression evaluation](#claim-shared.evaluation), stores the result in a fresh
variable, and removes the statement:

\\[
\frac{
\href{#claim-shared.evaluation}{\Delta\vdash\langle S,e\rangle\Downarrow\langle S',r\rangle}
\quad x\notin\operatorname{dom}(V')
}{
\Delta\vdash\langle S,(\mathsf{let}\ x=e)::P\rangle
\longrightarrow\langle\langle O',V'[x\mapsto r],\nu'\rangle,P\rangle
}
\quad\text{Let}
\\]

where \\(S'=\langle O',V',\nu'\rangle\\), and \\(V'[x\mapsto r]\\) adds
variable \\(x\\) holding \\(r\\). The remaining statements keep their order.
If evaluation fails or the variable already exists, there is no transition.
All argument evaluations belong to this one step; there is no separately
observable state partway through a failed expression.
```

```{definition} shared.executions
:lean: Shared/Step:Steps
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
:lean: Shared/Step:Stuck
:uses: shared.steps shared.finished shared.give

A configuration is *stuck* when statements remain but no
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
:uses: shared.state shared.syntax shared.give shared.steps shared.evaluation

Use classes `Token {}` and `Box { value }`. Let object \\(\mathsf{obj}(0)\\) be a token and
object \\(\mathsf{obj}(1)\\) a box, with these slots and allocation counter \\(2\\):

| Slot | Contents |
| --- | --- |
| `b` | Unique owner of box \\(\mathsf{obj}(1)\\) |
| `t` | Empty |
| Box \\(\mathsf{obj}(1)\\), field `value` | Unique owner of token \\(\mathsf{obj}(0)\\) |

Use the [give-share evaluation](#claim-shared.evaluation):

```dada
let s = b→share;
```

Variable `s` receives a shared owner of box \\(\mathsf{obj}(1)\\), and `b` becomes empty.
The field remains a unique owner of token \\(\mathsf{obj}(0)\\). The objects, empty `t`,
and allocation counter are unchanged.
````

````{example} shared.example.shared_middle
:lean: Shared/Examples:nested_shared_path
:uses: shared.example.share_value shared.resolution shared.give shared.steps shared.evaluation shared.state

Start again from the final state of {anchor-ref}`shared.example.share_value`,
before copying its field. Execute:

```dada
let outer = new Box(s→);
let u = outer.value.value→;
```

The [constructor](#claim-shared.evaluation) copies shared variable `s` into the new box \\(\mathsf{obj}(2)\\); `s`
remains initialized. Variable `outer` uniquely owns box \\(\mathsf{obj}(2)\\). The give
then traverses three references: unique `outer`, shared `outer.value` to box
\\(\mathsf{obj}(1)\\), and the unique `value` field of box \\(\mathsf{obj}(1)\\) to token \\(\mathsf{obj}(0)\\).

[Resolving](#claim-shared.resolution) the shared middle link makes this a shared access even though the first and
last stored references are unique. The give changes only the reference in box
\\(\mathsf{obj}(1)\\)'s `value` field to shared, and `u` receives a shared owner of token \\(\mathsf{obj}(0)\\). `outer`
stays unique; its field stays shared; `s` still refers to box \\(\mathsf{obj}(1)\\).
All three objects remain in the [object table](#claim-shared.state), and the allocation counter is \\(3\\).
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
:lean: Shared/State:References Shared/Soundness:Owners Shared/Soundness:Compatible Shared/Soundness:WellFormed
:uses: shared.state shared.allocated shared.programs

A [state](#claim-shared.state) is well formed, written \\(\mathsf{WF}_{\Delta}(S)\\), when:

- Object identities and variable names are each distinct.
- Every object's class is [declared](#claim-shared.programs), and its distinct field names match the
  declaration's order, including fields whose slots are empty.
- Every [allocated identity](#claim-shared.allocated) has an index below the allocation counter. Field
  references target objects with strictly smaller indices.
- Every stored reference targets an allocated object, and every allocated
  object has at least one stored owning reference.
- Any two distinct owning occurrences targeting the same object are both shared.

Owning occurrences are counted across all variable slots and all object fields.
The last condition permits several shared references to an object, but a stored
unique reference must be its only incoming owning reference. That local condition
does not by itself give a path unique access: every preceding reference must
also be unique. The older-object condition follows construction order and prevents
an owner-only cycle with no variable root.
```

```{theorem} shared.path_exclusivity
:lean: Shared/Liveness:WellFormed.path_mode_exclusive
:uses: shared.well_formed shared.resolution

In a [well-formed state](#claim-shared.well_formed), no object can be reached both by an entirely unique
path and by a path containing a shared reference:

\\[
\begin{aligned}
&\href{#claim-shared.well_formed}{\mathsf{WF}_{\Delta}(S)}\;\land\;
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
:lean: Shared/Liveness:WellFormed.live_iff_allocated
:uses: shared.well_formed shared.live shared.allocated

In a [well-formed state](#claim-shared.well_formed), an object is live exactly when it is allocated:

\\[
\href{#claim-shared.well_formed}{\mathsf{WF}_{\Delta}(S)}
\quad\Longrightarrow\quad
\bigl(\href{#claim-shared.live}{\mathsf{Live}_S(\alpha)}\iff\href{#claim-shared.allocated}{\mathsf{Allocated}_S(\alpha)}\bigr).
\\]

Every allocated object therefore has an owning path from a variable. Sharing
allows several such paths without making missing objects reachable.
```

```{theorem} shared.soundness
:lean: Shared/Soundness:Steps.from_initial
:uses: shared.state shared.syntax shared.give shared.steps shared.well_formed shared.liveness shared.path_exclusivity shared.programs shared.executions shared.machine shared.evaluation shared.well_formed_classes

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
:lean: Correspondence/UniqueShared:embedId Correspondence/UniqueShared:embedReference Correspondence/UniqueShared:embedSlots Correspondence/UniqueShared:embedObject Correspondence/UniqueShared:embedState Correspondence/UniqueShared:embedPlace Correspondence/UniqueShared:embedValue Correspondence/UniqueShared:embedStatement Correspondence/UniqueShared:embedClasses Correspondence/UniqueShared:embedProgram Correspondence/UniqueShared:embedConfiguration
:uses: given.classes given.state given.syntax given.unpacking shared.state shared.syntax shared.references given.programs given.machine

The Shared language contains a translation of the [Given fragment with
single-variable bindings](given.md#claim-given.syntax). This section restricts the correspondence to that
fragment. Write
\\(E\\) for this translation, applied to programs, configurations, and their
components.

For a [state](given.md#claim-given.state), \\(E\\) replaces every reference \\(\alpha\\) with the unique
[reference](#claim-shared.references) \\((\mathsf{unique},\alpha)\\). Empty slots remain empty. Class names,
field names, variable names, object identities, table order, and the next-identity
counter are preserved.

For a [program](given.md#claim-given.programs), \\(E\\) preserves its class declarations, places, constructors,
gives, and statement order. It introduces no give-share expression. For a
[configuration](given.md#claim-given.machine), it translates both the state and the remaining code. Thus a
related pair describes the same point in the same computation, with explicit
unique mode tags in the Shared state.
```

```{theorem} shared.correspondence
:lean: Correspondence/UniqueShared:step_correspondence
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
:lean: Correspondence/UniqueShared:boundary_correspondence
:uses: given.syntax given.steps shared.syntax shared.steps shared.embedding shared.correspondence given.machine shared.machine shared.finished given.finished shared.stuck given.stuck

For every program in the Given fragment with single-variable bindings,
[translating](#claim-shared.embedding) its [initial configuration](given.md#claim-given.machine) gives exactly the [initial configuration](#claim-shared.machine)
of its translated Shared program.

For every configuration in this fragment, the translated configuration is [finished](#claim-shared.finished) exactly
when the original is [finished](given.md#claim-given.finished). Using the program's class table, the translated
configuration is [stuck](#claim-shared.stuck) exactly when the original is [stuck](given.md#claim-given.stuck). The correspondence
therefore agrees on how execution starts, on successful completion, and on the
absence of an available step before completion.
```
