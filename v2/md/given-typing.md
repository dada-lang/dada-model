# Given: typing and soundness

```{definition} given.typing.declarations
:lean: Unique/Views:TypedClass Unique/Views:ClassTable
:uses: given.classes given.programs given.patterns given.unpacking given.evaluation

The type system checks that each give finds a value and that each binding can
receive its result. A move changes the source's type description as well as its
contents.

This chapter uses the unpacking extension {anchor-ref}`given.unpacking`;
[expression evaluation](given.md#claim-given.evaluation) is unchanged.

A *typed class table* \\(\Sigma\\) gives each field a declared class:

\\[
\begin{aligned}
d &::= \mathsf{class}\ C\ \{f_1:C_1,\ldots,f_n:C_n\},\\
\Sigma &\in \mathsf{ClassName}\rightharpoonup
  \mathsf{List}(\mathsf{FieldName}\times\mathsf{ClassName}).
\end{aligned}
\\]

Fields retain their constructor-argument order.

Field declarations constrain the class of an object stored there. They do not
require its slot to remain initialized after a move. All value types in this
chapter are nominal types; ownership is unique.
```

```{definition} given.typing.well_formed_classes
:lean: Unique/Views:ClassTable.WellFormed
:uses: given.typing.declarations

A [typed class table](#claim-given.typing.declarations) is *well formed* when
each class name has one declaration, field names within each declaration are
distinct, and every field's declared class occurs in \\(\Sigma\\).
```

```{definition} given.typing.erasure
:lean: Unique/Views:ClassTable.erase
:uses: given.typing.declarations given.programs

*Class-table erasure* removes field types to recover the
[operational class table](given.md#claim-given.programs): if \\(\href{#claim-given.typing.declarations}{\Sigma(C)}=[f_1:C_1,\ldots,f_n:C_n]\\), then
\\(\lfloor\Sigma\rfloor(C)=[f_1,\ldots,f_n]\\).
```

## Types describe accessible places

```{definition} given.typing.paths
:lean: Unique/Views:Path
:uses: given.typing.declarations

A *relative place* \\(\rho\\) is a finite sequence of field names.
The empty sequence \\(\epsilon\\) denotes the value itself; concatenation is
written \\(\rho\cdot\sigma\\); \\(\rho f\\) appends the single field \\(f\\).

\\[\rho ::= \epsilon \mid f\cdot\rho.\\]
```

```{definition} given.typing.class_at
:lean: Unique/Views:classAt
:uses: given.typing.paths given.typing.declarations

A [relative path](#claim-given.typing.paths) is *valid from* \\(C\\) when its fields
can be followed through the [declarations](#claim-given.typing.declarations) in \\(\Sigma\\).
Write \\(\operatorname{class}_{\Sigma}(C,\rho)\\) for its final declared class;
in particular, \\(\operatorname{class}_{\Sigma}(C,\epsilon)=C\\).
```

```{definition} given.typing.views
:lean: Unique/Views:Entry Unique/Views:ViewType Unique/Views:ViewType.whole
:uses: given.typing.paths given.typing.class_at

A *view entry* \\(a\\), in the category \\(\mathsf{ViewEntry}\\), is a positive
[relative place](#claim-given.typing.paths) or a negative nonempty relative place. A *view* \\(A\\) is a
finite set of entries. A *type* \\(T\\) always pairs a nominal class with a view:

\\[
\begin{aligned}
a &::= \rho \mid -\rho \qquad(\text{negative entries require }\rho\ne\epsilon),\\
A &\subseteq_{\mathrm{fin}}\mathsf{ViewEntry},\\
T &::= C.A.
\end{aligned}
\\]

The surface notation uses braces: `Point.{x, -y}`. A positive entry exposes an
initialized value of the path's declared class, including its fully initialized
fields. A negative entry exposes an existing empty slot. Every proper prefix
of either kind of entry must hold an object. A branch not covered by an entry
is unknown and cannot be accessed through this type.

We write bare \\(C\\) as shorthand for \\(C.\{\epsilon\}\\): the whole value,
including all fields reachable from it, is initialized. It is not a separate
form of type. By contrast, \\(C.\{\}\\) exposes the object itself but none of
its fields. The empty path \\(\epsilon\\) and the empty set \\(\{\}\\) have
different meanings.
```

```{definition} given.typing.base
:lean: Unique/Views:ViewType
:uses: given.typing.views

The *base class* is \\(\operatorname{base}(C.A)=C\\).
```

```{definition} given.typing.well_formed_types
:lean: Unique/Views:Entry.valid Unique/Views:entriesDisjoint Unique/Views:ViewType.WellFormed
:uses: given.typing.views given.typing.base given.typing.class_at

A type is *well formed* when its [base class](#claim-given.typing.base) is declared and its view satisfies
the following condition.

**Entries do not overlap.** Their paths must be [valid from](#claim-given.typing.class_at)
\\(C\\), distinct, and pairwise prefix-incomparable: no entry's path is a prefix
of another's. Thus `C.{f, -f.g}` is not a valid view. Exposing all of `f` would
claim initialization that `-f.g` denies. To describe such a hole, first expand
`f` into its fields.
```

````{example} given.typing.example.views
:lean: Unique/ViewChecks:view_information
:uses: given.typing.views given.typing.full

A *full view* accounts for every field recursively, including fields known to
be empty. A *partial view* leaves some statuses unknown. The [formal fullness predicate](#claim-given.typing.full) comes after this example;
only this distinction is needed to read the table.

Consider these declarations:

```dada
class Token {}
class Pair { left: Token, right: Token }
class Box { item: Pair }
```

| Type | Information available |
| --- | --- |
| `Pair` | Both fields contain tokens. |
| `Pair.{left}` | `left` contains a token; `right` is unknown. |
| `Pair.{-left, right}` | `left` is empty and `right` contains a token: a full view. |
| `Box.{-item.left}` | `item` contains a pair whose `left` is empty; its `right` is unknown. |
| `Box.{-item.left, item.right}` | `item` contains a pair whose `left` is empty and `right` contains a token: a full view. |

In the last two types, `item` itself remains initialized. Its negative child
does not make the containing field empty.
````

```{definition} given.typing.observations
:lean: Unique/Views:positive Unique/Views:negative Unique/Views:Pos Unique/Views:Neg
:uses: given.typing.views given.typing.class_at

Each [type](#claim-given.typing.views) determines a set of *known-initialized paths*
\\(\operatorname{pos}_{\Sigma}(T)\\) and *known-empty paths*
\\(\operatorname{neg}_{\Sigma}(T)\\). These sets give precise meanings to
the view notation.

For \\(T=C.A\\):

- \\(\epsilon\\) is positive: the described value is an object.
- Every proper prefix of an entry's path is positive.
- A positive entry's path and all its [valid descendants](#claim-given.typing.class_at) are positive.
- Exactly the paths of negative entries are negative.

No other path is known. In particular, a negative path does not say that its
descendants are empty: there is no object in that slot whose fields could be
examined.
The shorthand \\(C=C.\{\epsilon\}\\) makes every valid path positive.
```

```{definition} given.typing.full
:lean: Unique/Views:Full
:uses: given.typing.observations given.typing.class_at given.typing.base

A view is *full* when every direct field of every known-initialized object has
a known status:

\\[
\mathsf{Full}_{\Sigma}(T)\iff
\begin{gathered}
  \forall\rho\in\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T).\\
  \forall(f:D)\in\Sigma(\href{#claim-given.typing.class_at}{\operatorname{class}}_{\Sigma}(\href{#claim-given.typing.base}{\operatorname{base}}(T),\rho)).\\
  \rho f\in\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T)\cup\href{#claim-given.typing.observations}{\operatorname{neg}}_{\Sigma}(T).
\end{gathered}
\\]

A full view may contain empty slots; being full does not mean being fully
initialized.
```

## Normalizing a view

````{example} given.typing.example.normalization
:lean: Unique/ViewChecks:normalize_nested_whole
:uses: given.typing.observations given.typing.normalization given.typing.well_formed_types

Several spellings can describe the same accessible fields:

```dada
class Foo { bar: Bar }
class Bar { baz: Baz }
class Baz {}
```

In `Foo.{bar.baz}`, `bar` must contain an object, and its only field, `baz`,
is fully initialized. We can therefore write `bar` instead. The same reasoning
then applies to the whole `Foo`:

\\[
\mathsf{Foo}.\{\mathsf{bar.baz}\}
\;\leadsto\;\mathsf{Foo}.\{\mathsf{bar}\}
\;\leadsto\;\mathsf{Foo}.\{\epsilon\}
\;=\;\mathsf{Foo}.
\\]

All these spellings are [well formed](#claim-given.typing.well_formed_types).
The [normalization procedure defined next](#claim-given.typing.normalization)
chooses the last one; this example illustrates only the collapses it performs.
If `Bar` also declared another field, an unknown or empty sibling would prevent
the first collapse. A deeper path remains when it describes only part of an
intermediate object.
````

```{definition} given.typing.normalization
:lean: Unique/Views:Entry.dropPrefix Unique/Views:Entry.prepend Unique/Views:normalizeEntries Unique/Views:normalize Unique/Views:Normalized
:uses: given.typing.observations given.typing.example.normalization given.typing.class_at

*Normalization* \\(\mathsf{N}_{\Sigma}(T)\\) replaces a completely exposed
subtree with its shortest positive entry. Work from the deepest entries
toward the root. If the [class at](#claim-given.typing.class_at) \\(\rho\\) declares exactly the nonempty list
of fields \\(f_1,\ldots,f_n\\), replace all their positive entries together:

\\[
A\cup\{\rho f_1,\ldots,\rho f_n\}
\;\leadsto\;
A\cup\{\rho\}
\qquad(n>0).
\\]

Here none of the replaced entries occurs in \\(A\\). Repeat until no such
replacement is possible. A negative or unknown child prevents a collapse.
The procedure shortens the finite paths in the view; it does not unfold
recursive class declarations.

Keep a positive entry for an empty-class object: it records that the object
exists. Do not create an entry for an unknown field merely because its declared
class is empty. The root is already known to exist, so for an empty class
\\(C\\), normalize \\(C.\{\}\\) to \\(C.\{\epsilon\}\\).

Print \\(C.\{\epsilon\}\\) as \\(C\\). Expanded spellings remain valid input.
The typing rules use normalized types throughout, including when comparing
constructor arguments with their declared types.
```

```{theorem} given.typing.normalization_correct
:lean: Unique/Normalization:normalization_correct
:uses: given.typing.normalization given.typing.observations given.typing.base given.typing.well_formed_classes given.typing.well_formed_types

For a [well-formed class table](#claim-given.typing.well_formed_classes) \\(\Sigma\\) and
[well-formed type](#claim-given.typing.well_formed_types) \\(T\\), [normalization](#claim-given.typing.normalization) preserves
the [base class](#claim-given.typing.base), well-formedness, and every initialization fact:

\\[
\begin{aligned}
\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(\href{#claim-given.typing.normalization}{\mathsf N}_{\Sigma}(T))
  &= \href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T),\\
\href{#claim-given.typing.observations}{\operatorname{neg}}_{\Sigma}(\href{#claim-given.typing.normalization}{\mathsf N}_{\Sigma}(T))
  &= \href{#claim-given.typing.observations}{\operatorname{neg}}_{\Sigma}(T),\\
\href{#claim-given.typing.normalization}{\mathsf N}_{\Sigma}(\href{#claim-given.typing.normalization}{\mathsf N}_{\Sigma}(T)) &= \href{#claim-given.typing.normalization}{\mathsf N}_{\Sigma}(T).
\end{aligned}
\\]

Reordering a view's entries gives the same normalized type. Once normalized,
a second pass makes no further change.
```

## Reading and updating a view

```{definition} given.typing.focus
:lean: Unique/Views:focus
:uses: given.typing.normalization given.typing.example.views given.typing.base given.typing.class_at given.typing.observations given.typing.paths

*Focusing* a type at an initialized [relative place](#claim-given.typing.paths) returns the current type of
the value stored there, including any holes. Write \\(T\downarrow\rho\\);
it is defined only when \\(\rho\in\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T)\\).

Start from \\(\href{#claim-given.typing.normalization}{\mathsf{N}}_{\Sigma}(T)\\).
Focusing at \\(\epsilon\\) returns that type. For a nonempty path, let
\\(D=\href{#claim-given.typing.class_at}{\operatorname{class}}_{\Sigma}(\href{#claim-given.typing.base}{\operatorname{base}}(T),\rho)\\).

- If a positive entry's path is a prefix of \\(\rho\\), including an entry
  at \\(\epsilon\\), the result is \\(D\\), the whole-type shorthand.
- Otherwise, retain the entries below \\(\rho\\), remove their common prefix
  \\(\rho\\), and attach the resulting view to \\(D\\). Normalize the result.

For example, under the [example declarations](#claim-given.typing.example.views):

\\[
\mathsf{Box}.\{-\mathsf{item.left},\mathsf{item.right}\}
  \downarrow\mathsf{item}
=
\mathsf{Pair}.\{-\mathsf{left},\mathsf{right}\}.
\\]

This operation does not restore fields that have been moved or hidden.
```

```{definition} given.typing.emptying
:lean: Unique/Views:remainingAfterMove Unique/Views:emptyPath
:uses: given.typing.focus given.typing.observations given.typing.normalization given.typing.example.views

*Emptying* an initialized nonempty path updates its enclosing type. Write
\\(T[-\rho]\\), where \\(\rho\in\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T)\\).
The result records that this slot is now empty and preserves the information
about every other branch.

Compute the update as follows:

1. [Normalize](#claim-given.typing.normalization) the input type.
2. Expand any positive entry that is a strict prefix of \\(\rho\\) into its
   declared fields, including an entry at \\(\epsilon\\). Continue only along
   the finite path to \\(\rho\\).
3. Remove all entries at or below \\(\rho\\), then insert \\(-\rho\\).
   Normalize the result.

An expansion cannot pass through an empty class, because no longer valid path
exists there. This procedure also handles a target that is already the common
prefix of several view entries.

For the [example's `Box`](#claim-given.typing.example.views), moving `item.left` yields:

\\[
\mathsf{Box}[-\mathsf{item.left}]
=
\mathsf{Box}.\{-\mathsf{item.left},\mathsf{item.right}\}.
\\]

The preserved sibling is essential. Replacing the result with
`Box.{-item.left}` would also forget access to `item.right`.
An empty or unknown target has no emptying operation.
```

```{definition} given.typing.forgetting
:lean: Unique/Views:Subtype
:uses: given.typing.normalization given.typing.example.views given.typing.observations given.typing.base

A value can be used through a view that provides less information.
To compare types, first [normalize](#claim-given.typing.normalization) them. For the normalized types \\(T\\) and
\\(U\\), write \\(T\preceq_{\Sigma}U\\) when they have the same [base class](#claim-given.typing.base) and:

\\[
\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(U)\subseteq\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T),
\qquad
\href{#claim-given.typing.observations}{\operatorname{neg}}_{\Sigma}(U)\subseteq\href{#claim-given.typing.observations}{\operatorname{neg}}_{\Sigma}(T).
\\]

This *view weakening* can forget initialization facts and access. It cannot
invent them. For the [example declarations](#claim-given.typing.example.views),
`Pair` can be weakened to `Pair.{left}`, but neither
`Pair.{left}` nor `Pair.{}` can be strengthened to `Pair`.
Unknown does not imply empty. Compare the known paths, not just the written
entries: the single root entry in `Pair` includes both of its fields.

Weakening does not change storage, copy a reference, or abandon an object's
ownership. Hidden fields remain part of the owned object graph.
```

## Typing expressions

```{definition} given.typing.environments
:lean: Unique/Typing:SlotDescription Unique/Typing:Environment Unique/Typing:Admissible Unique/Typing:Environment.WellFormed Unique/Typing:Environment.lookup Unique/Typing:Environment.replace
:uses: given.typing.views given.typing.well_formed_types given.typing.normalization given.syntax

A *slot description* \\(B\\) says that a slot is empty or contains a value of
a particular type. A *typing environment* \\(\Gamma\\) describes every allocated
variable slot:

\\[
B ::= 0 \mid T,
\qquad
\Gamma\in\mathsf{VariableId}\rightharpoonup B.
\\]

Here \\(B\\) also denotes the set of slot descriptions generated by its grammar.
The marker \\(0\\) describes an empty slot; it is not a value type.
All types in an environment must be [well formed](#claim-given.typing.well_formed_types) and [normalized](#claim-given.typing.normalization) under \\(\Sigma\\).
An empty variable remains in \\(\operatorname{dom}(\Gamma)\\); its name cannot
be reused by a fresh binding. An absent variable has no description.
```

```{definition} given.typing.take
:lean: Unique/Typing:splitPlace Unique/Typing:take
:uses: given.typing.environments given.typing.paths given.typing.focus given.typing.observations given.typing.emptying given.syntax

To check a give, find the variable where the path starts, then follow its
fields inside that variable's type. For `b.item.left`, the variable is `b`
and the [relative place](#claim-given.typing.paths) is `item.left`. Giving `b` itself has no field suffix.

Thus every [place expression](given.md#claim-given.syntax) has a unique decomposition \\(p=x.\rho\\), with
\\(x.\epsilon=x\\). *Taking* a place returns its current type and updates that
variable's [environment description](#claim-given.typing.environments). Define \\(\mathsf{take}_{\Sigma}(\Gamma,p)=(T,\Gamma')\\)
when \\(\Gamma(x)=U\\), \\(\rho\in\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(U)\\), and:

\\[
T=U\href{#claim-given.typing.focus}{\downarrow}\rho,
\qquad
\Gamma'=
\begin{cases}
\Gamma[x\mapsto 0] & \rho=\epsilon,\\
\Gamma[x\mapsto \href{#claim-given.typing.emptying}{U[-\rho]}] & \rho\ne\epsilon.
\end{cases}
\\]

All other variables keep their descriptions.
Taking an absent variable, an empty slot, or an unknown field is undefined.
```

```{example} given.typing.example.take
:lean: Unique/TypingChecks:take_root_and_field
:uses: given.typing.environments given.typing.example.views given.typing.paths given.typing.take

Suppose \\(\Gamma(b)=\mathsf{Box}\\), using the `Box`, `Pair`, and `Token`
[declarations above](#claim-given.typing.example.views). The following are two separate [takes](#claim-given.typing.take) from that starting
environment:

| Give | Root and [relative place](#claim-given.typing.paths) | Result type | Updated description of `b` |
| --- | --- | --- | --- |
| `b→` | \\(b,\epsilon\\) | `Box` | `0` |
| `b.item.left→` | \\(b,\mathsf{item.left}\\) | `Token` | `Box.{-item.left, item.right}` |

The first takes the whole box. The second takes one token, leaving the box,
the pair, and its other token accessible through `b`. Both leave every other
variable's description unchanged.
```

```{definition} given.typing.expressions
:lean: Unique/Typing:ExprTyped Unique/Typing:ArgsTyped
:uses: given.typing.declarations given.typing.environments given.typing.forgetting given.evaluation given.typing.take

*Expression typing* records both the value produced and the [environment](#claim-given.typing.environments) after
its moves:

\\[
\Sigma;\Gamma\vdash e:T\;\triangleright\;\Gamma'.
\\]

The **Give** rule uses the current view of the source:

\\[
\frac{\href{#claim-given.typing.take}{\mathsf{take}}_{\Sigma}(\Gamma,p)=(T,\Gamma')}
{\Sigma;\Gamma\vdash p\mathord{\to}:T\;\triangleright\;\Gamma'}
\quad\text{Give}
\\]

**Construct** checks arguments from left to right, passing each updated
environment to the next argument:

\\[
\frac{
  \begin{gathered}
    \href{#claim-given.typing.declarations}{\Sigma(C)}=[f_1:C_1,\ldots,f_n:C_n]\\
    \Sigma;\Gamma_{i-1}\vdash e_i:C_i\;\triangleright\;\Gamma_i
      \quad(1\leq i\leq n)
  \end{gathered}
}{
  \Sigma;\Gamma_0\vdash\mathsf{new}\ C(e_1,\ldots,e_n):C
    \;\triangleright\;\Gamma_n
}
\quad\text{Construct}
\\]

For no arguments, the environment is unchanged. The argument count must match
the declaration. Each argument supplies an owning value, so the new object has
fully initialized fields.

A result may expose [less information](#claim-given.typing.forgetting):

\\[
\frac{
  \Sigma;\Gamma\vdash e:T\;\triangleright\;\Gamma'
  \qquad T\href{#claim-given.typing.forgetting}{\preceq}_{\Sigma}U
}{
  \Sigma;\Gamma\vdash e:U\;\triangleright\;\Gamma'
}
\quad\text{Weaken}
\\]

**First-pass restriction.** Constructor arguments must have their whole declared
class types. A partially moved object can be transferred to another variable or
unpacked, but cannot be passed to a constructor requiring its whole class.
This rejects some dynamically safe programs. The [Future extensions](dada/future-extensions.md)
chapter records the proposed generic-view constructor signatures.
```

## Typing bindings and statements

```{definition} given.typing.field
:lean: Unique/Typing:fieldDescription
:uses: given.typing.environments given.typing.focus given.typing.observations

The *direct-field description* records whether a field has the [empty-slot description](#claim-given.typing.environments) or gives its current type:

\\[
\mathsf{field}_{\Sigma}(T,f)=
\begin{cases}
0 & f\in\href{#claim-given.typing.observations}{\operatorname{neg}}_{\Sigma}(T),\\
T\href{#claim-given.typing.focus}{\downarrow} f & f\in\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T).
\end{cases}
\\]

It is undefined if that field is unknown.
```

```{definition} given.typing.bindings
:lean: Unique/Typing:FieldBindings Unique/Typing:BindingTyped
:uses: given.patterns given.typing.environments given.typing.field given.typing.base given.typing.declarations

*Binding typing*, written \\(\Sigma;\Gamma\vdash b:T\Rightarrow\Gamma'\\),
describes where an expression's result goes. A [variable pattern](given.md#claim-given.patterns) transfers its
current type unchanged:

\\[
\frac{x\notin\operatorname{dom}(\Gamma)}
{\Sigma;\Gamma\vdash x:T\Rightarrow\Gamma[x\mapsto T]}
\quad\text{Bind}
\\]

An [unpacking pattern](given.md#claim-given.patterns) must name every
declared field, and each [field's description](#claim-given.typing.field) must be defined:

\\[
\frac{
  \begin{gathered}
    \href{#claim-given.typing.base}{\operatorname{base}}(T)=C
    \qquad\href{#claim-given.typing.declarations}{\Sigma(C)}=[f_1:C_1,\ldots,f_n:C_n]\\
    \href{#claim-given.typing.field}{\mathsf{field}}_{\Sigma}(T,f_i)=B_i\quad(1\leq i\leq n)\\
    x_1,\ldots,x_n\text{ are distinct}
    \qquad x_i\notin\operatorname{dom}(\Gamma)\quad(1\leq i\leq n)
  \end{gathered}
}{
  \Sigma;\Gamma\vdash C\mathord{\to}\{f_1:x_1,\ldots,f_n:x_n\}:T
    \Rightarrow\Gamma[x_1\mapsto B_1,\ldots,x_n\mapsto B_n]
}
\quad\text{Unpack}
\\]

The rule displays fields in declaration order; named patterns can be reordered
to that order. A known-empty field produces an empty binding. An initialized
field transfers its current type, which may itself be a partial view.

Knowing every direct field's status is sufficient: unpacking does not inspect
the interiors of the objects transferred. An unknown direct field prevents
this rule from applying. It cannot be silently dropped or assigned an invented
initialization status.
```

```{definition} given.typing.statements
:lean: Unique/Typing:StatementTyped
:uses: given.typing.expressions given.typing.bindings given.patterns

*Statement typing*, written \\(\Sigma;\Gamma\vdash t\Rightarrow\Gamma'\\),
first [types the expression](#claim-given.typing.expressions) and then
[its binding pattern](#claim-given.typing.bindings):

\\[
\frac{
  \Sigma;\Gamma\vdash e:T\;\href{#claim-given.typing.expressions}{\triangleright}\;\Gamma_1
  \qquad \href{#claim-given.typing.bindings}{\Sigma;\Gamma_1\vdash b:T\Rightarrow\Gamma_2}
}{
  \Sigma;\Gamma\vdash\mathsf{let}\ b=e\Rightarrow\Gamma_2
}
\quad\text{Let}
\\]
```

```{definition} given.typing.sequences
:lean: Unique/Typing:SequenceTyped
:uses: given.typing.statements given.programs

A *statement-sequence typing* \\(\Sigma;\Gamma\vdash P\Rightarrow\Gamma_f\\)
threads [statement typings](#claim-given.typing.statements) through the remaining code:

\\[
\frac{}{\Sigma;\Gamma\vdash []\Rightarrow\Gamma}
\qquad
\frac{
  \href{#claim-given.typing.statements}{\Sigma;\Gamma\vdash t\Rightarrow\Gamma_1}
  \qquad\Sigma;\Gamma_1\vdash P\Rightarrow\Gamma_f
}{
  \Sigma;\Gamma\vdash t::P\Rightarrow\Gamma_f
}.
\\]
```

```{definition} given.typing.programs
:lean: Unique/Typing:ProgramTyped
:uses: given.typing.sequences given.typing.well_formed_classes

A program is well typed when \\(\Sigma\\) is [well formed](#claim-given.typing.well_formed_classes) and
\\(\href{#claim-given.typing.sequences}{\Sigma;\varnothing\vdash P\Rightarrow\Gamma_f}\\) for some final environment
\\(\Gamma_f\\). Finishing retains storage, so the final environment need not
be empty. Scope exit and destruction are not part of this language.
```

## A nested move followed by unpacking

````{example} given.typing.example.moves
:lean: Unique/TypingExecutionChecks:moves_and_unpacking
:uses: given.typing.example.views given.typing.statements given.unpacking

With the `Token`, `Pair`, and `Box` [declarations above](#claim-given.typing.example.views):

```dada
let b = new Box(new Pair(new Token(), new Token()));
let taken = b.item.left→;
let p = b.item→;
let Pair → { left, right } = p→;
```

The [statement rules](#claim-given.typing.statements) change the following entries; all others keep their descriptions.
The marker `0` means that a variable exists with an empty slot.

| Statement | Updated binding | New bindings |
| --- | --- | --- |
| Construct | — | `b: Box` |
| Give `left` | `b: Box.{-item.left, item.right}` | `taken: Token` |
| Give `item` | `b: Box.{-item}` | `p: Pair.{-left, right}` |
| Unpack | `p: 0` | `left: 0`, `right: Token` |

[Unpacking](given.md#claim-given.unpacking) consumes the pair object; the box and both tokens remain.
A subsequent `left→` has no typing derivation, because `left` is empty.
Nor can `p→` be repeated.
````

````{example} given.typing.example.rejections
:lean: Unique/TypingRejectionChecks:rejected_moves
:uses: given.typing.example.views given.typing.expressions given.typing.bindings

The [expression](#claim-given.typing.expressions) and [binding](#claim-given.typing.bindings) rules distinguish failure from lack of knowledge:

- From `p: Pair.{-left, right}`, `p.left→` is rejected because the field is
  known empty.
- From `p: Pair.{right}`, the same expression is rejected because `left` is
  unknown. It might exist and be initialized at runtime.
- From `p: Pair.{-left, right}`, giving `p→` succeeds statically with that
  same viewed type. It does not produce a whole `Pair`.
- Passing that result to `new Box(p→)` is rejected by this first constructor
  rule, even though the untyped machine could put the partial pair in the box.
- Unpacking `Pair.{right}` is rejected because it would need a description
  for the hidden `left` field.

[Constructor argument order](#claim-given.typing.expressions) also matters:

```dada
class Two { a: Token, b: Token }
let t = new Token();
let bad = new Two(t→, t→);
```

The first argument leaves `t: 0`. The second argument therefore has no typing
derivation. Constructor arguments are checked in the same order as evaluation.
````

## Relating types to storage

```{definition} given.typing.read
:lean: Unique/TypingRealization:readPath
:uses: given.typing.paths given.state given.lookup

*Reading a relative path*, written \\(\mathsf{read}_S(\alpha,\rho)\\), starts
at object \\(\alpha\\) and follows the fields of the
[relative path](#claim-given.typing.paths) \\(\rho\\). At \\(\epsilon\\), it returns \\(\alpha\\)
if the object exists. At a nonempty path, every intermediate slot must contain
an existing object; the final slot may contain an object identity or
\\(\bot\\). A missing object or field encountered while following the path,
or an empty intermediate slot, makes the read undefined. The final identity
is not dereferenced.
```

```{definition} given.typing.satisfaction
:lean: Unique/TypingRealization:Satisfies
:uses: given.typing.read given.typing.base given.typing.class_at given.typing.observations given.allocated

An object *satisfies* a type, written \\(\Sigma;S\models\alpha:T\\), when:

- \\(O(\alpha)\\) exists and has class \\(\href{#claim-given.typing.base}{\operatorname{base}}(T)\\).
- For every \\(\rho\in\href{#claim-given.typing.observations}{\operatorname{pos}}_{\Sigma}(T)\\),
  \\(\href{#claim-given.typing.read}{\mathsf{read}}_S(\alpha,\rho)=\beta\\) for an [allocated object](given.md#claim-given.allocated) \\(\beta\\)
  of class \\(\href{#claim-given.typing.class_at}{\operatorname{class}}_{\Sigma}(\href{#claim-given.typing.base}{\operatorname{base}}(T),\rho)\\).
- For every \\(\rho\in\href{#claim-given.typing.observations}{\operatorname{neg}}_{\Sigma}(T)\\),
  \\(\href{#claim-given.typing.read}{\mathsf{read}}_S(\alpha,\rho)=\bot\\).

Omitted branches impose no local initialization requirement. The definition
ranges over finite paths; recursive class declarations need no infinite
syntactic unfolding.
```

```{definition} given.typing.realization
:lean: Unique/TypingRealization:FieldsMatchClasses Unique/TypingRealization:PendingValues Unique/TypingRealization:Realizes
:uses: given.typing.satisfaction given.typing.environments given.typing.erasure given.well_formed given.state given.typing.well_formed_types given.typing.well_formed_classes

Expression results can temporarily own objects before binding or construction.
Let \\(R\\) be a finite ordered list of pairs \\((\alpha:T)\\) for these
*pending values*. Write \\(\Sigma;\Gamma\models(S;R)\\) when all of the following hold:

1. Storage satisfies {anchor-ref}`given.well_formed`, with the references in
   \\(R\\) counted alongside stored references in the ownership condition.
   Thus every allocated object has exactly one owner, including hidden fields
   and pending values.
2. Every occupied object field targets an object of its declared nominal
   class in \\(\Sigma\\). This condition applies even to fields hidden by views.
3. \\(\operatorname{dom}(\Gamma)=\operatorname{dom}(V)\\). If
   \\(\Gamma(x)=0\\), then \\(V(x)=\bot\\). If \\(\Gamma(x)=T\\), then
   \\(V(x)=\alpha\\) and \\(\href{#claim-given.typing.satisfaction}{\Sigma;S\models\alpha:T}\\).
4. Each \\((\alpha:T)\\) in \\(R\\) satisfies \\(\href{#claim-given.typing.satisfaction}{\Sigma;S\models\alpha:T}\\).

Here \\(\Sigma\\) is a [well-formed typed class table](#claim-given.typing.well_formed_classes),
\\(S=\langle O,V,\nu\rangle\\), and the operational class table is
\\(\href{#claim-given.typing.erasure}{\lfloor\Sigma\rfloor}\\). Types must be [well formed](#claim-given.typing.well_formed_types) and
[normalized](#claim-given.typing.normalization) throughout.
Empty pending lists are written \\([]\\).

This relation does not require every allocated object to satisfy its whole
class type. That would rule out the very field moves the views describe.
```

```{definition} given.typing.execution
:lean: Unique/Unpacking:Steps Unique/TypingSafety:StepsExactly
:uses: given.unpacking given.executions

Write \\(\longrightarrow_u^{*}\\) for zero or more [extended steps](given.md#claim-given.unpacking), using the
reflexive and transitive rules of {anchor-ref}`given.executions` with
\\(\longrightarrow_u\\) in place of \\(\longrightarrow\\).
Write \\(K\longrightarrow_u^k K'\\) for exactly \\(k\\) extended steps.
```

```{definition} given.typing.stuck
:lean: Unique/Unpacking:Stuck
:uses: given.unpacking given.finished

A configuration is *stuck in the extended language* when it is not [finished](given.md#claim-given.finished) and
has no \\(\href{given.html#claim-given.unpacking}{\longrightarrow_u}\\) successor. Finishing still means that no
statements remain.
```

```{definition} given.typing.configurations
:lean: Unique/TypedConfigurations:ConfigurationTyped
:uses: given.typing.realization given.typing.sequences given.typing.well_formed_classes given.machine

A [configuration](given.md#claim-given.machine) is *well typed with final environment* \\(\Gamma_f\\) when its
storage [realizes an environment](#claim-given.typing.realization) under which its remaining [statements typecheck](#claim-given.typing.sequences):

\\[
\Sigma\vdash\langle S,P\rangle:\Gamma_f
\iff
\exists\Gamma.\;
  \href{#claim-given.typing.realization}{\Sigma;\Gamma\models(S;[])}
  \;\land\;
  \href{#claim-given.typing.sequences}{\Sigma;\Gamma\vdash P\Rightarrow\Gamma_f}.
\\]

This judgment requires a [well-formed](#claim-given.typing.well_formed_classes) \\(\Sigma\\). The current environment may
change at each step; \\(\Gamma_f\\) describes the same final bindings throughout
the execution.
```

## Progress and preservation

```{lemma} given.typing.expression_soundness
:lean: Unique/TypingSafety:expression_soundness
:uses: given.typing.expressions given.typing.realization given.evaluation given.typing.well_formed_classes given.typing.erasure

[Expression typing](#claim-given.typing.expressions) guarantees both successful evaluation and the
description of its result. For every [well-formed](#claim-given.typing.well_formed_classes) \\(\Sigma\\), environment
\\(\Gamma\\), storage \\(S\\), and [pending-value list](#claim-given.typing.realization) \\(R\\), assume:

\\[
\Sigma;\Gamma\vdash e:T\;\href{#claim-given.typing.expressions}{\triangleright}\;\Gamma',
\qquad
\href{#claim-given.typing.realization}{\Sigma;\Gamma\models(S;R)}.
\\]

Then an evaluation exists:

\\[
\exists S',\alpha.\;
\href{#claim-given.typing.erasure}{\lfloor\Sigma\rfloor}\vdash\langle S,e\rangle
  \href{given.html#claim-given.evaluation}{\Downarrow}\langle S',\alpha\rangle.
\\]

Moreover, **every** such evaluation satisfies:

\\[
\href{#claim-given.typing.realization}{\Sigma;\Gamma'\models(S';R\mathbin{+\!\!+}[(\alpha:T)])}.
\\]

Here \\(+\!\!+\\) appends lists. Earlier constructor arguments are included in
\\(R\\) while later arguments run. The lemma preserves their types as well
as the variables' types. Evaluation leaves the variable domain unchanged, so
the typing rules' freshness checks also hold at the point of runtime binding.
```

```{theorem} given.typing.progress
:lean: Unique/TypingSafety:ConfigurationTyped.progress
:uses: given.typing.configurations given.typing.expression_soundness given.typing.bindings given.finished given.unpacking given.typing.erasure

For every [well-typed configuration](#claim-given.typing.configurations), either execution has [finished](given.md#claim-given.finished) or a next
[step](given.md#claim-given.unpacking) is possible:

\\[
\href{#claim-given.typing.configurations}{\Sigma\vdash K:\Gamma_f}
\quad\Longrightarrow\quad
\href{given.html#claim-given.finished}{\mathsf{Finished}}(K)
\;\lor\;
\exists K'.\;\href{#claim-given.typing.erasure}{\lfloor\Sigma\rfloor}\vdash K\href{given.html#claim-given.unpacking}{\longrightarrow_u} K'.
\\]

This is a claim about the operational rules: typing does not add a transition
for an otherwise failing operation.
```

```{theorem} given.typing.preservation
:lean: Unique/TypingSafety:ConfigurationTyped.preservation
:uses: given.typing.configurations given.typing.expression_soundness given.typing.bindings given.unpacking given.typing.erasure

Every [step](given.md#claim-given.unpacking) from a [well-typed configuration](#claim-given.typing.configurations) preserves its typing:

\\[
\frac{
  \href{#claim-given.typing.configurations}{\Sigma\vdash K:\Gamma_f}
  \qquad \href{#claim-given.typing.erasure}{\lfloor\Sigma\rfloor}\vdash K\href{given.html#claim-given.unpacking}{\longrightarrow_u} K'
}{
  \href{#claim-given.typing.configurations}{\Sigma\vdash K':\Gamma_f}
}.
\\]

The existential current environment changes to reflect moved slots and new
bindings. The final environment stays the same. This theorem quantifies over
every operational successor, including unpacking an object with empty fields.
```

```{theorem} given.typing.safety
:lean: Unique/TypingSafety:program_safety
:uses: given.typing.configurations given.typing.progress given.typing.preservation given.typing.statements given.typing.programs given.typing.stuck given.typing.well_formed_classes given.typing.sequences given.typing.erasure given.state given.typing.execution given.finished given.unpacking given.empty_state

A [well-typed program](#claim-given.typing.programs) cannot reach a [stuck configuration](#claim-given.typing.stuck). For a [well-formed](#claim-given.typing.well_formed_classes)
\\(\Sigma\\), if

\\[
\href{#claim-given.typing.sequences}{\Sigma;\varnothing\vdash P\Rightarrow\Gamma_f},
\qquad
\href{#claim-given.typing.erasure}{\lfloor\Sigma\rfloor}\vdash
  \langle \href{given.html#claim-given.empty_state}{S_{\emptyset}},P\rangle\href{#claim-given.typing.execution}{\longrightarrow_u^{*}}K,
\\]

then \\(K\\) is [finished](given.md#claim-given.finished) or has a [next step](given.md#claim-given.unpacking).

In this straight-line language, each step removes one statement and adds none.
Every execution of a well-typed program can therefore be extended to a finished
one whose total length is exactly the initial statement count. The final storage
still owns its remaining objects; this result does not require their destruction.
```
