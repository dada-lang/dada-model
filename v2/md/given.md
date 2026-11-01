# Given: operational semantics

```{definition} given.classes
:lean: Unique/Syntax:ClassName Unique/Syntax:FieldName Unique/Syntax:Class

This language studies transfer of ownership. Variables and object fields hold
references to objects. Giving a reference moves it to its destination and leaves
its source empty; constructing an object moves references into its fields.

A *class declaration* \\(d\\) names a class and its fields. Write \\(C\\) for
a class name in \\(\mathsf{ClassName}\\), and \\(f\\) for a field name in
\\(\mathsf{FieldName}\\). The field count \\(n\\) is a natural number,
including zero:

\\[
d ::= \mathsf{class}\ C\ \{f_1,\ldots,f_n\}.
\\]

Fields are distinct and listed in constructor-argument order. They have names
but no declared types.
An empty class still has objects, so this language needs no primitive values.
Subscripts and primes distinguish names in the same category.
```

## Places, expressions, and statements

```{definition} given.syntax
:lean: Unique/Syntax:VariableId Unique/Syntax:Place Unique/Syntax:Value Unique/Syntax:Statement
:uses: given.classes

A *place expression* \\(p\\) follows a route from a variable through zero or
more fields. Write \\(x\\) for a variable name in \\(\mathsf{VariableId}\\).
A *value expression* \\(e\\) produces an owning reference. Giving a place,
`p→`, is the only way to obtain a value from an existing place. A constructor
creates an object from the values of its argument expressions:

\\[
\begin{aligned}
p &::= x \mid p.f \\
e &::= p\mathord{\to} \mid \mathsf{new}\ C(e_1,\ldots,e_n).
\end{aligned}
\\]

Constructor arguments can themselves be constructors or gives of places.

A *statement* \\(t\\) determines what the machine executes next. In this
language, the only statement evaluates an expression and binds its result to a
fresh variable:

\\[
t ::= \mathsf{let}\ x=e.
\\]

Expressions evaluate within a statement; they do not choose the next statement.
Each `let` introduces a distinct runtime variable. This fragment has no shadowing,
scopes, function calls, assignment, or destruction.
```

## Programs

```{definition} given.programs
:lean: Unique/Syntax:Classes Unique/Syntax:Program Unique/Soundness:ClassesWellFormed
:uses: given.classes given.syntax

A *program* \\(\Pi\\) supplies class declarations and an ordered sequence of
statements. Its *class table* \\(\Delta\\) maps each declared class name to
its field names in declaration order. Each class name is declared once.

Write \\(A\rightharpoonup B\\) for finite partial maps from domain \\(A\\)
to codomain \\(B\\), and \\(\mathsf{List}(A)\\) for finite ordered sequences
of elements of \\(A\\). A *statement sequence* \\(P\\) is empty, written
\\([]\\), or has a first statement \\(t\\) followed by a sequence \\(P\\),
written \\(t::P\\):

\\[
\begin{aligned}
\Delta &\in \mathsf{ClassName}\rightharpoonup\mathsf{List}(\mathsf{FieldName}) \\
P &::= [] \mid t::P \\
\Pi &::= \langle\Delta,P\rangle.
\end{aligned}
\\]

For a declaration \\(\mathsf{class}\ C\ \{f_1,\ldots,f_n\}\\), the table
contains \\(\Delta(C)=[f_1,\ldots,f_n]\\). The class table is *well formed*
when each such list has distinct field names.
```

## Objects and slots

```{definition} given.state
:lean: Unique/Syntax:ObjectId Unique/State:Slot Unique/State:Object Unique/State:State Unique/State:State.empty
:uses: given.classes given.syntax given.programs

An *object identity* \\(\alpha\\) is a tagged natural number. The tag keeps
identities distinct from ordinary numbers. We also use \\(\beta\\) for an
object identity; \\(\operatorname{index}\\) extracts its number:

\\[
\alpha,\beta\in\mathsf{ObjectId}
  =\{\mathsf{obj}(n)\mid n\in\mathbb N\},
\qquad
\operatorname{index}(\mathsf{obj}(n))=n.
\\]

A *slot* is a variable or object field. Its *contents* \\(s\\), in the
category \\(\mathsf{Slot}\\), are empty, written \\(\bot\\), or hold a
reference to an object. An *object* \\(o\\), in the category
\\(\mathsf{Object}\\), has a class name and an ordered list of named field
slots. All references in this language are owners:

\\[
\begin{aligned}
s &::= \bot \mid \alpha \\
o &::= C\{f_1:s_1,\ldots,f_n:s_n\}.
\end{aligned}
\\]

A *storage state* \\(S\\) has an *object table* \\(O\\), a *variable table*
\\(V\\), and an *allocation counter* \\(\nu\\):

\\[
\begin{aligned}
O &\in \mathsf{ObjectId}\rightharpoonup\mathsf{Object} \\
V &\in \mathsf{VariableId}\rightharpoonup\mathsf{Slot} \\
\nu &\in \mathbb N \\
S &::= \langle O,V,\nu\rangle.
\end{aligned}
\\]

The counter supplies \\(\mathsf{obj}(\nu)\\) for the next allocation, then
increases by one. Write \\(\varnothing\\) for an empty map; the *empty state*
is \\(S_{\emptyset}=\langle\varnothing,\varnothing,0\rangle\\).
Finite-map notation assumes distinct keys. The well-formedness conditions below
enforce this for the tables and field lists.
The tables and field lists record empty slots as well as occupied ones.
```

```{definition} given.storage_places
:lean: Unique/State:StoragePlace Unique/State:Stored Unique/State:Updated
:uses: given.syntax given.state

A *storage place* \\(q\\) selects one slot directly: either a variable or a
field of a particular object:

\\[
q ::= x \mid \alpha.f.
\\]

A place expression such as `b.value` describes a route to a slot; a storage place
such as \\(\mathsf{obj}(1).\mathsf{value}\\) identifies the slot itself.

For \\(S=\langle O,V,\nu\rangle\\), write \\(S[q]=s\\) for *slot lookup*.
It is a partial operation, defined by:

\\[
\begin{aligned}
S[x] &= V(x) &&\text{when }V(x)\text{ is defined}, \\
S[\alpha.f_i] &= s_i
  &&\text{when }O(\alpha)=C\{f_1:s_1,\ldots,f_n:s_n\},\ 1\leq i\leq n.
\end{aligned}
\\]

Lookup has no result for an absent variable, object, or field. An existing empty
slot has the defined result \\(\bot\\). An occupied slot contains an object
identity, not that object's data; the data is in \\(O\\).

For an existing slot, \\(S[q\leftarrow s]\\) replaces its contents and leaves
all other slots, object identities, class names, and the counter unchanged.
This update preserves the slot even when its new contents are \\(\bot\\).
```

## The machine

```{definition} given.machine
:lean: Unique/State:Configuration Unique/State:Configuration.initial Unique/State:Configuration.finished Unique/Step:Step Unique/Step:Steps Unique/Step:Stuck
:uses: given.programs given.state

A *machine configuration* \\(K\\) pairs its storage with the statements
still to run:

\\[
K ::= \langle S,P\rangle.
\\]

For a program \\(\Pi=\langle\Delta,P\rangle\\), execution starts at
\\(\langle S_{\emptyset},P\rangle\\). The class table \\(\Delta\\) stays
fixed during execution.

One *step*, written \\(\Delta\vdash K\longrightarrow K'\\), executes the
first statement, updates storage, and removes that statement from the sequence.
The operational rules below define this judgment. Expression evaluation completes
within a step; the machine never exposes a partially evaluated expression.

A configuration is *finished* exactly when no statements remain:

\\[
\mathsf{Finished}(\langle S,P\rangle)\iff P=[].
\\]

The final storage remains available; finishing does not discard its objects or
variables.
```

## Operational semantics

### Resolving a place

```{definition} given.resolution
:lean: Unique/Step:Resolve
:uses: given.storage_places

*Place resolution*, written \\(S\vdash p\Downarrow q:\alpha\\), follows
route \\(p\\) to a storage place \\(q\\) holding reference \\(\alpha\\).
These two rules define it:

\\[
\frac{S[x]=\alpha}{S\vdash x\Downarrow x:\alpha}
\quad\text{Variable}
\\]

\\[
\frac{
  S\vdash p\Downarrow q:\beta
  \qquad S[\beta.f]=\alpha
}{S\vdash p.f\Downarrow\beta.f:\alpha}
\quad\text{Field}
\\]

Each slot along the route must hold a reference. Undefined lookup and the empty
contents \\(\bot\\) satisfy neither rule's lookup premise. Resolution itself
changes nothing.
```

### Evaluating an expression

```{definition} given.evaluation
:lean: Unique/Step:Eval Unique/Step:EvalArgs Unique/Step:State.allocate
:uses: given.classes given.syntax given.programs given.state given.storage_places given.resolution

*Expression evaluation*, written

\\[
\Delta\vdash\langle S,e\rangle\Downarrow\langle S',\alpha\rangle,
\\]

produces an owning reference \\(\alpha\\) and updated storage \\(S'\\).
The following rules define successful evaluation, including nested expressions.

**Give.** Resolve the place and empty its slot. Return the reference taken:

\\[
\frac{S\vdash p\Downarrow q:\alpha}{
  \Delta\vdash\langle S,p\mathord{\to}\rangle
  \Downarrow\langle S[q\leftarrow\bot],\alpha\rangle
}
\quad\text{Give}
\\]

**Construct.** Evaluate the arguments from left to right, then allocate the
object and put their results into its fields in declaration order.

\\[
\frac{
  \begin{gathered}
    \Delta(C)=[f_1,\ldots,f_n] \\
    \Delta\vdash\langle S_{i-1},e_i\rangle
      \Downarrow\langle S_i,\alpha_i\rangle
      \quad\text{for each }i=1,\ldots,n \\
    \beta\notin\operatorname{dom}(O_n)
  \end{gathered}
}{
  \Delta\vdash\langle S_0,\mathsf{new}\ C(e_1,\ldots,e_n)\rangle
    \Downarrow\langle S',\beta\rangle
}
\quad\text{Construct}
\\]

where \\(S_0\\) is the starting storage and \\(S_i\\) is the storage after
the first \\(i\\) arguments, with

\\[
\begin{aligned}
S_n &= \langle O_n,V_n,\nu_n\rangle, \\
\beta &= \mathsf{obj}(\nu_n), \\
O' &= O_n[\beta\mapsto C\{f_1:\alpha_1,\ldots,f_n:\alpha_n\}], \\
S' &= \langle O',V_n,\nu_n+1\rangle.
\end{aligned}
\\]

Here \\(\operatorname{dom}(O_n)\\) is the set of allocated identities, and
\\(O_n[\beta\mapsto o]\\) adds the fresh object's entry.

With no arguments, there are no argument premises and allocation uses
\\(S_n=S_0\\). Argument results remain owned by the ongoing evaluation until
placed in the new object's fields; they are not copied.

An empty slot, a missing field, or an unknown class has no successful evaluation.
Giving the same slot twice as constructor arguments fails on the second give.
An expression runs within one statement transition, but it can still fail.
```

### Executing a statement

```{definition} given.steps
:lean: Unique/Step:State.bind Unique/Step:Step
:uses: given.machine given.evaluation

To execute `let x = e`, evaluate the expression completely, then put its result
in the new variable `x`. For the resulting storage
\\(S'=\langle O',V',\nu'\rangle\\), write \\(V'[x\mapsto\alpha]\\) for the
variable table extended with that binding, and abbreviate the updated state as:

\\[
S'[x\mapsto\alpha]=\langle O',V'[x\mapsto\alpha],\nu'\rangle.
\\]

The *domain* \\(\operatorname{dom}(V')\\) is the set of variable names already
present.

This is the only statement-transition rule:

\\[
\frac{
  \begin{gathered}
    \Delta\vdash\langle S,e\rangle\Downarrow\langle S',\alpha\rangle \\
    S'=\langle O',V',\nu'\rangle
    \qquad x\notin\operatorname{dom}(V')
  \end{gathered}
}{
  \Delta\vdash\langle S,(\mathsf{let}\ x=e)::P\rangle
  \longrightarrow\langle S'[x\mapsto\alpha],P\rangle
}
\quad\text{Let}
\\]

The remaining statements keep their order. If evaluation fails or the variable
already exists, the statement has no transition. There is no recovery transition
or separately observable state partway through a failed expression. A finished
configuration has no statement to execute, so it takes no step.
```

### Finite executions and failure

```{definition} given.executions
:lean: Unique/Step:Steps Unique/Step:Stuck
:uses: given.machine given.steps

A *finite execution*, written \\(\Delta\vdash K\longrightarrow^{*}K'\\),
consists of zero or more steps. These rules define it:

\\[
\frac{}{\Delta\vdash K\longrightarrow^{*}K}
\qquad
\frac{
  \Delta\vdash K\longrightarrow K'
  \qquad \Delta\vdash K'\longrightarrow^{*}K''
}{\Delta\vdash K\longrightarrow^{*}K''}.
\\]

A configuration is *stuck* when statements remain but no next step is possible:

\\[
\mathsf{Stuck}_{\Delta}(K)\iff
\neg\mathsf{Finished}(K)\;\land\;
\neg\exists K'.\;\Delta\vdash K\longrightarrow K'.
\\]

This is how execution *goes wrong*. For example, trying to give through an absent
variable or an empty field yields no expression evaluation and therefore no
statement step. Undefined lookup alone is a property of storage; attempting an
operation that requires that lookup is what leaves the machine stuck.
```

## Worked executions

````{example} given.example.token
:lean: Unique/Examples:create_token
:uses: given.classes given.syntax given.programs given.machine given.steps

An empty class provides a value we can move:

```dada
class Token {}
class Box { value }
let t = new Token();
```

Starting with empty storage, one step creates a `Token` object and puts its
reference in `t`. The configuration is finished: no statements remain.
````

````{example} given.example.field
:lean: Unique/Examples:give_execution
:uses: given.classes given.syntax given.programs given.machine given.steps

A field can receive a reference and later give it away:

```dada
class Token {}
class Box { value }

let t = new Token();
let b = new Box(t→);
let u = b.value→;
```

Starting with empty storage, the machine takes three steps:

1. Create the token and put its reference in `t`.
2. Create a box and move `t` into its `value` field, leaving `t` empty.
3. Follow `b` to the box and move the field's reference into `u`.

The resulting configuration is finished. Variable `b` owns the box and `u`
owns the token; `t` and the box's `value` field are empty. Giving the field moves
its contents; the containing box remains in place.
````

````{example} given.example.nested
:lean: Unique/Examples:nested_constructor
:uses: given.classes given.syntax given.evaluation given.steps

Constructor arguments can create their own objects:

```dada
class Token {}
class Box { value }
let b = new Box(new Token());
```

Starting with empty storage, this is one statement step. Evaluate `new Token()`
first, then put its reference in the newly created box's `value` field. Bind the
box's reference to `b`. The finished configuration contains both objects, with
no temporary source variable needed in the program.
````

````{example} given.example.empty_field
:lean: Unique/Examples:second_give_fails
:uses: given.example.field given.executions

Starting with the final storage of {anchor-ref}`given.example.field`, try:

```dada
let v = b.value→;
```

Let \\(\Delta\\) be that example's class table, and let \\(K_{\mathrm{bad}}\\)
pair its final storage with this one remaining statement.
It is stuck: `b` still holds the box's reference, but its `value` field is empty.
The give cannot evaluate, so the statement cannot execute. Giving once leaves
no reference behind for a second give.

Execution from this configuration cannot finish:

\\[
\neg\exists K'.\;
\bigl(\Delta\vdash K_{\mathrm{bad}}\longrightarrow^{*}K'\bigr)
\;\land\;\mathsf{Finished}(K').
\\]

Zero steps leave the statement pending, and a nonempty execution would need a
first step, which does not exist.
````

## Liveness and well-formedness

```{definition} given.well_formed
:lean: Unique/State:Allocated Unique/State:Live Unique/State:References Unique/Soundness:WellFormed Unique/Soundness:WellFormedWith
:uses: given.programs given.state given.storage_places given.evaluation

The following conditions describe storage between statements, including before
the first statement. References held temporarily during expression evaluation
are accounted for within that evaluation.

For \\(S=\langle O,V,\nu\rangle\\), an object is *allocated* when its identity
occurs in the object table:

\\[
\mathsf{Allocated}_S(\alpha)\iff\alpha\in\operatorname{dom}(O).
\\]

An object is *live* when an owning path reaches it from a variable. Write
\\(\mathsf{Live}_S(\alpha)\\) for the judgment defined by these two rules:

\\[
\frac{S[x]=\alpha}{\mathsf{Live}_S(\alpha)}
\qquad
\frac{\mathsf{Live}_S(\beta)\qquad S[\beta.f]=\alpha}{\mathsf{Live}_S(\alpha)}.
\\]

An empty slot contributes no edge to such a path. Allocation and liveness are
properties of the object graph, independent of how the state was produced.

Write \\(\mathsf{WF}_{\Delta}(S)\\) when the state meets all these conditions:

- Object-table keys and variable names are each distinct.
- Every object's class is declared. Its field names occur exactly in declaration
  order, without duplicates, including fields whose slots are empty.
- Every allocated identity \\(\alpha\\) satisfies
  \\(\operatorname{index}(\alpha)<\nu\\). A reference in an object's field
  targets an older object: its index is strictly smaller than the containing
  object's index.
- The references in **all variable slots and all object fields**, counted by
  occurrence, contain each allocated object identity exactly once and contain
  no other identity.

The last condition excludes both duplicate ownership and references to missing
objects. Two slots containing the same identity count as two references even
though their contents are equal. The age condition records the construction
order: a newly constructed object receives previously existing objects as its
fields. It excludes cycles of objects owning one another without a variable root.
```

```{theorem} given.liveness
:lean: Unique/Liveness:WellFormed.live_iff_allocated
:uses: given.well_formed

In every well-formed state, an object is live exactly when it is allocated:

\\[
\mathsf{WF}_{\Delta}(S)
\quad\Longrightarrow\quad
\bigl(\mathsf{Live}_S(\alpha)\iff\mathsf{Allocated}_S(\alpha)\bigr).
\\]

Thus every allocated object has an owning path from a variable, and following
owning paths cannot reach a missing object.
```

```{theorem} given.single_owner
:lean: Unique/Liveness:WellFormed.owner_count
:uses: given.well_formed

In every well-formed state, each allocated object has exactly one owning
reference across all variable slots and object fields. This counts the slot
that immediately holds its reference: a path through several enclosing objects
does not add extra owners of its final target.
```

```{theorem} given.soundness
:lean: Unique/Soundness:Steps.from_initial
:uses: given.programs given.executions given.well_formed given.liveness given.single_owner

For any program with a well-formed class table, every configuration reached by
a finite execution from its empty initial state has a well-formed state.
This includes zero steps, intermediate configurations, and completed executions.

Consequently, every allocated object remains live and has exactly one owning
reference. The theorem covers successful execution; it does not promise that a
program can always take another step.
```

## Proposed extension: unpacking

```{definition} given.patterns
:status: draft
:uses: given.classes given.syntax

An *unpacking pattern* consumes an object and transfers its field slots into
new variables. This extends the statement syntax with a *binding pattern*
\\(b\\):

\\[
\begin{aligned}
b &::= x \mid C\mathord{\to}\{f_1:x_1,\ldots,f_n:x_n\} \\
t &::= \mathsf{let}\ b=e.
\end{aligned}
\\]

In a pattern, `f: x` names the field `f` and its new variable `x`; `f` alone is
shorthand for `f: f`. The pattern must name every declared field exactly once,
and its variable names must be distinct. Fields may be listed in any order.
This first version has flat patterns, with no `_` or `..` entries.

The expression `p→` transfers the reference out of `p`. The pattern
`C → { ... }` then removes the enclosing object and transfers its components.
An ordinary field give leaves the enclosing object in place. An empty class
can be consumed with `C → {}`.

This section proposes the operational extension used by the typing chapter.
The preceding Lean definitions and proved results cover the original
single-variable bindings; they do not yet include unpacking.
```

```{definition} given.unpacking
:status: draft
:uses: given.patterns given.state given.evaluation given.steps

To execute `let C → { ... } = e`, evaluate `e`, check that its result names a
`C` object, and transfer that object's slots into fresh variables. An initialized
field becomes an initialized variable; an empty field becomes an empty variable.
The consumed object's entry is removed from the object table.

Write \\(\Delta\vdash K\longrightarrow_u K'\\) for the extended transition
relation. It has the earlier **Let** rule, read over the extended statement
syntax, and the following **Unpack** rule. We display the pattern fields in
declaration order:

\\[
\frac{
  \begin{gathered}
    \Delta\vdash\langle S,e\rangle\Downarrow\langle S',\alpha\rangle \\
    \Delta(C)=[f_1,\ldots,f_n]
    \qquad S'=\langle O',V',\nu'\rangle \\
    O'(\alpha)=C\{f_1:s_1,\ldots,f_n:s_n\} \\
    x_1,\ldots,x_n\text{ are distinct}
    \qquad x_i\notin\operatorname{dom}(V')\quad(1\leq i\leq n)
  \end{gathered}
}{
  \Delta\vdash
    \langle S,(\mathsf{let}\ C\mathord{\to}\{f_1:x_1,\ldots,f_n:x_n\}=e)::P\rangle
    \longrightarrow_u\langle S'',P\rangle
}
\quad\text{Unpack}
\\]

where

\\[
S''=\left\langle
  O'\setminus\{\alpha\},\;
  V'[x_1\mapsto s_1,\ldots,x_n\mapsto s_n],\;
  \nu'
\right\rangle.
\\]

Here \\(O'\setminus\{\alpha\}\\) removes the object-table entry for
\\(\alpha\\). The variable-map extension adds exactly the displayed slots,
including those containing \\(\bot\\). All other objects and variables, and
the allocation counter, retain their values from \\(S'\\).

The slots move together within one statement step. No object stored in a field
is removed by unpacking its container. A class mismatch or an already allocated
destination variable gives this rule no transition, even when that variable's
slot is empty.
```

````{example} given.example.unpack
:status: draft
:uses: given.patterns given.unpacking given.machine

Unpacking also works after a field has been moved:

```dada
class Token {}
class Pair { left, right }

let p = new Pair(new Token(), new Token());
let taken = p.left→;
let Pair → { left, right } = p→;
```

After the proposed three-step execution, `taken` owns the first token and
`right` owns the second. Variables `p` and `left` have empty slots. The pair
object has been removed; both token objects remain. No statements remain.

The empty field does not produce a value: its new binding `left` is empty too.
Trying to evaluate `left→` afterward would have no result.
````
