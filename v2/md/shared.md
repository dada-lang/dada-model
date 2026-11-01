# Shared: operational semantics

```{definition} shared.give
:lean: Shared/State:Mode Shared/State:Reference Shared/State:Slot Shared/Syntax:Place Shared/Step:Resolve Shared/Step:Take Shared/Step:Promote Shared/Step:Give Shared/Soundness:Compatible

Shared ownership lets several references own the same object. A reference has
an object identity and a mode: *unique* or *shared*. The object itself has no
ownership mode. Variables and object fields are slots, each empty or holding
one reference.

A *place expression* \\(p\\) follows fields from a variable to select a slot. Giving it, `p→`,
requires every slot and intermediate object on the route to exist, and every
slot to hold a reference. It moves the reference when every reference along
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

```{definition} shared.syntax
:lean: Shared/Syntax:ClassName Shared/Syntax:FieldName Shared/Syntax:VariableId Shared/Syntax:Class Shared/Syntax:Classes Shared/Syntax:Place Shared/Syntax:Value Shared/Syntax:Statement Shared/Syntax:Program Shared/Step:Step
:uses: shared.give given.programs

A *class* named \\(C\\), in \\(\mathsf{ClassName}\\), declares an ordered
list of \\(n\\) fields, where \\(n\\) is a natural number including zero.
A *field name* \\(f\\) belongs to \\(\mathsf{FieldName}\\). Constructor
arguments supply the fields in order. Fields have no declared types; all values
are objects.

A *variable name* \\(x\\) belongs to \\(\mathsf{VariableId}\\). A place
expression \\(p\\) starts at a variable and follows fields. A *value
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

The expression `p→share` performs the give, then makes its result a shared owner.
Giving along a unique route empties the source. To share a newly constructed
object, first construct it in a variable, then give-share that variable.

A program has a class table \\(\Delta\\) and a finite sequence of `let`
statements. Each `let` names a fresh runtime variable. Constructor arguments are
value expressions, evaluated from left to right; they may themselves construct objects.
There is no shadowing, scope, call, assignment, destruction, or borrowing in this
fragment.
```

## Copying a field

````{example} shared.example.copy_field
:lean: Shared/Examples:sharing_execution
:uses: shared.syntax shared.give

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

```{definition} shared.state
:lean: Shared/Syntax:ObjectId Shared/Syntax:Class Shared/Syntax:Classes Shared/Soundness:ClassesWellFormed Shared/State:Mode Shared/State:Reference Shared/State:Reference.owned Shared/State:Reference.shared Shared/State:Slot Shared/State:Object Shared/State:State Shared/State:StoragePlace Shared/State:Stored Shared/State:State.empty
:uses: shared.give shared.syntax given.programs

An object has an identity \\(\alpha\\), a class name, and named field slots.
A *reference* \\(r\\) pairs a *mode* \\(\kappa\\) with an object identity.
*Slot contents* \\(s\\) are either empty, \\(\bot\\), or a reference:

\\[
\begin{aligned}
\kappa &::= \mathsf{unique}\mid\mathsf{shared} \\
r &::= (\kappa,\alpha) \\
s &::= \bot\mid r.
\end{aligned}
\\]

A state \\(S=\langle O,V,\nu\rangle\\) consists of the object table,
variable table, and allocation counter \\(\nu\\). An object identity is a tagged
natural number \\(\mathsf{obj}(n)\\), with \\(\operatorname{index}(\mathsf{obj}(n))=n\\).
Creation uses \\(\mathsf{obj}(\nu)\\), then increments the counter. The empty
state has empty tables and counter zero.

The tables are finite maps, with distinct keys required by well-formedness:

\\[
O\in\mathsf{ObjectId}\rightharpoonup\mathsf{Object},\qquad
V\in\mathsf{VariableId}\rightharpoonup\mathsf{Slot},\qquad
\nu\in\mathbb N.
\\]

A *storage place* \\(q\\) selects one slot: variable \\(x\\), or field
\\(\alpha.f\\) of a particular object. Write \\(S[q]=s\\) for its contents.
An empty slot still exists; lookup at an absent variable or field is undefined.
The reference identifies an object in \\(O\\); the slot does not contain that
object's data.

Object identities, variable names, and field names within each object are
distinct in the states described here. A well-formed class table has distinct
class names and distinct field names within each declaration.
```

## Reading a route

```{definition} shared.resolution
:lean: Shared/State:Mode.join Shared/Step:Resolve
:uses: shared.state shared.syntax

Resolving a place reads its route without changing the state. Write
\\(S\vdash p\Downarrow q:\alpha@\kappa\\) when the route selects slot
\\(q\\) and object \\(\alpha\\), with effective access mode \\(\kappa\\).
The effective mode describes the entire route, not just the last stored reference.

A variable starts with its stored reference's mode. To resolve \\(p.f\\),
first resolve \\(p\\), look up that object, then read field \\(f\\).
The resulting mode is unique only if both the route to the containing object
and the field's stored reference are unique:

\\[
\kappa_0\sqcup\kappa_1 =
\begin{cases}
\mathsf{unique} & \kappa_0=\mathsf{unique}\ \land\ \kappa_1=\mathsf{unique},\\
\mathsf{shared} & \text{otherwise}.
\end{cases}
\\]

Thus once a shared reference occurs along a path, the rest of that path has
shared access. An absent variable, a missing field or intermediate object, or
an empty slot prevents resolution.
```

## Executing statements

```{definition} shared.steps
:lean: Shared/State:Configuration Shared/State:Configuration.initial Shared/State:Configuration.finished Shared/Step:Eval Shared/Step:EvalArgs Shared/Step:State.bind Shared/Step:State.allocate Shared/Step:Step Shared/Step:Steps Shared/Step:Stuck
:uses: shared.state shared.syntax shared.resolution shared.give

A *configuration* \\(\langle S,P\rangle\\) pairs storage \\(S\\) with an
ordered *statement sequence* \\(P\\): either empty, \\([]\\), or a statement
\\(t\\) followed by the rest, \\(t::P\\).
Execution starts with the empty state and the program's entire
statement sequence. It finishes when that sequence is empty, retaining the
final variables and objects.

Write \\(\Delta\vdash\langle S,P\rangle\longrightarrow
\langle S',P'\rangle\\) for one successful statement. Its destination variable
must be absent from the variable table. The step removes the first statement
and leaves the remaining code unchanged.

- `let x = p→` gives from \\(p\\) and stores the result in `x`.
- `let x = p→share` performs the same give, then stores a shared owner of the
  result's object in `x`.
- `let x = new C(e₁, …, eₙ)` evaluates its arguments from left to right,
  requiring one per declared field. After the arguments finish, it allocates
  a fresh object at \\(\mathsf{obj}(\nu)\\) and places their results in its fields.
  Variable `x` receives a unique owner of that object, and the counter advances.

An empty class takes no arguments. Repeated gives through shared access leave
the source initialized. A give through an entirely unique path empties its slot,
so a second give from that slot fails. All argument evaluations belong to the
statement's single transition. Argument results remain owned by the evaluation
until placed in the new object's fields.

A finite execution consists of zero or more successful steps. A configuration
is *stuck* when statements remain but no step is available.
```

## A shared link inside a path

````{example} shared.example.share_value
:lean: Shared/Examples:share_value
:uses: shared.state shared.syntax shared.give shared.steps

Use classes `Token {}` and `Box { value }`. Let object \\(\mathsf{obj}(0)\\) be a token and
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

Variable `s` receives a shared owner of box \\(\mathsf{obj}(1)\\), and `b` becomes empty.
The field remains a unique owner of token \\(\mathsf{obj}(0)\\). The objects, empty `t`,
and allocation counter are unchanged.
````

````{example} shared.example.shared_middle
:lean: Shared/Examples:nested_shared_path
:uses: shared.example.share_value shared.resolution shared.give shared.steps

Start again from the final state of {anchor-ref}`shared.example.share_value`,
before copying its field. Execute:

```dada
let outer = new Box(s→);
let u = outer.value.value→;
```

The constructor copies shared variable `s` into the new box \\(\mathsf{obj}(2)\\); `s`
remains initialized. Variable `outer` uniquely owns box \\(\mathsf{obj}(2)\\). The give
then traverses three references: unique `outer`, shared `outer.value` to box
\\(\mathsf{obj}(1)\\), and the unique `value` field of box \\(\mathsf{obj}(1)\\) to token \\(\mathsf{obj}(0)\\).

The shared middle link makes this a shared access even though the first and
last stored references are unique. The give changes only the reference in box
\\(\mathsf{obj}(1)\\)'s `value` field to shared, and `u` receives a shared owner of token \\(\mathsf{obj}(0)\\). `outer`
stays unique; its field stays shared; `s` still refers to box \\(\mathsf{obj}(1)\\).
All three objects remain allocated and the allocation counter is \\(3\\).
````

## Liveness and well-formedness

```{definition} shared.well_formed
:lean: Shared/State:Allocated Shared/State:Live Shared/State:References Shared/Soundness:Owners Shared/Soundness:Compatible Shared/Soundness:WellFormed
:uses: shared.state

An object is allocated when its identity appears in the object table. It is live
when an owning path reaches it from a variable, following initialized fields.
Both unique and shared references contribute owning edges. Empty slots contribute
none.

A state is well formed, written \\(\mathsf{WF}_{\Delta}(S)\\), when:

- Object identities and variable names are each distinct.
- Every object's class is declared, and its distinct field names match the
  declaration's order, including fields whose slots are empty.
- Every allocated identity has an index below the allocation counter. Field
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

In a well-formed state, no object can be reached both by an entirely unique
path and by a path containing a shared reference:

\\[
\begin{aligned}
&\mathsf{WF}_{\Delta}(S)\;\land\;
  (S\vdash p\Downarrow q:\alpha@\mathsf{unique})\\
&\quad\Longrightarrow\quad
  \neg\exists p',q'.\ S\vdash p'\Downarrow q':\alpha@\mathsf{shared}.
\end{aligned}
\\]

The paths start at variables. A unique reference stored inside a shared
container does not contradict this property: the path through that container
already contains a shared reference.
```

```{theorem} shared.liveness
:lean: Shared/Liveness:WellFormed.live_iff_allocated
:uses: shared.well_formed

In a well-formed state, an object is live exactly when it is allocated:

\\[
\mathsf{WF}_{\Delta}(S)
\quad\Longrightarrow\quad
\bigl(\mathsf{Live}_S(\alpha)\iff\mathsf{Allocated}_S(\alpha)\bigr).
\\]

Every allocated object therefore has an owning path from a variable. Sharing
allows several such paths without making missing objects reachable.
```

```{theorem} shared.soundness
:lean: Shared/Soundness:Steps.from_initial
:uses: shared.state shared.syntax shared.give shared.steps shared.well_formed shared.liveness shared.path_exclusivity

For any program with a well-formed class table, every configuration reached by
a finite execution from the empty initial state has a well-formed state. This
includes intermediate configurations and the state after the final statement.

Consequently, every allocated object remains live. In each such state, a unique
stored reference is the only incoming owner of its object; when an object has
several incoming owners, all those references are shared. No object has both
a unique path and a shared path from variables. This covers both explicit
give-share and copying through a shared path, including the change to the path's
final stored reference.
```

## The Given fragment inside Shared

```{definition} shared.embedding
:lean: Correspondence/UniqueShared:embedId Correspondence/UniqueShared:embedReference Correspondence/UniqueShared:embedSlots Correspondence/UniqueShared:embedObject Correspondence/UniqueShared:embedState Correspondence/UniqueShared:embedPlace Correspondence/UniqueShared:embedValue Correspondence/UniqueShared:embedStatement Correspondence/UniqueShared:embedClasses Correspondence/UniqueShared:embedProgram Correspondence/UniqueShared:embedConfiguration
:uses: given.classes given.state given.syntax shared.state shared.syntax

The Shared language contains a translation of the Given language. Write
\\(E\\) for this translation, applied to programs, configurations, and their
components.

For a state, \\(E\\) replaces every reference \\(\alpha\\) with the unique
reference \\((\mathsf{unique},\alpha)\\). Empty slots remain empty. Class names,
field names, variable names, object identities, table order, and the next-identity
counter are preserved.

For a program, \\(E\\) preserves its class declarations, places, constructors,
gives, and statement order. It introduces no give-share expression. For a
configuration, it translates both the state and the remaining code. Thus a
related pair describes the same point in the same computation, with explicit
unique mode tags in the Shared state.
```

```{theorem} shared.correspondence
:lean: Correspondence/UniqueShared:step_correspondence
:uses: given.steps shared.steps shared.embedding

For every class table \\(\Delta\\) and Given configuration \\(c\\), the
embedding matches steps in both directions:

- If \\(\Delta\vdash c\longrightarrow c'\\), then
  \\(E(\Delta)\vdash E(c)\longrightarrow E(c')\\).
- If \\(E(\Delta)\vdash E(c)\longrightarrow d\\), then there is a Given
  successor \\(c'\\) with \\(\Delta\vdash c\longrightarrow c'\\) and
  \\(d=E(c')\\).

The second statement covers every Shared successor \\(d\\); it does not
assume in advance that \\(d\\) is a translated state. These statements give
a one-step bisimulation between Given and its embedded fragment: Shared adds
no behavior to translated Given computations, and loses none of their steps.
```

```{theorem} shared.boundaries
:lean: Correspondence/UniqueShared:boundary_correspondence
:uses: given.syntax given.steps shared.syntax shared.steps shared.embedding shared.correspondence

For every Given program, translating its initial configuration gives exactly the
initial configuration of its translated Shared program.

For every Given configuration, the translated configuration is finished exactly
when the original is finished. Using the program's class table, the translated
configuration is stuck exactly when the original is stuck. The correspondence
therefore agrees on how execution starts, on successful completion, and on the
absence of an available step before completion.
```
