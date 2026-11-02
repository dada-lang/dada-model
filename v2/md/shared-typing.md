# Shared: typing and soundness

## When a give copies

````{example} shared.typing.example.copy
:lean: Shared/TypingExecutionChecks:copying_through_shared
:uses: shared.example.copy_field given.typing.views shared.give given.patterns shared.typing.types

The type of a place tells us whether giving it [moves or copies](shared.md#claim-shared.give).
Consider a box whose field has type `Token`:

```dada
class Token {}
class Box { item: Token }

let b = new Box(new Token());
let s = b→share;
let u = s.item→;
let v = s.item→;
```

| Statement | Result type | Effect on the source |
| --- | --- | --- |
| Construct `b` | `Box` | — |
| Give-share `b` | `shared Box` | `b` becomes empty. |
| Give `s.item` into `u` | `shared Token` | The field stays initialized. |
| Give `s.item` into `v` | `shared Token` | The field stays initialized. |

The field is declared `Token`, but access through `s` makes its effective type
`shared Token`. The first field give changes its stored reference to shared and
returns a shared copy; the second copies it again. Neither changes `s`'s type.

The [permission grammar below](#claim-shared.typing.types) formalizes the two
labels used here, `given` and `shared`. This example needs only their move/copy
distinction. The chapter adds these permissions to
[Given's types and views](given-typing.md#claim-given.typing.views).
`Token` is shorthand for `given Token`. It also carries
[Given's unpacking patterns](given.md#claim-given.patterns) into Shared, with
unpacking restricted to unique results.
````

## Permissions and field declarations

```{definition} shared.typing.types
:lean: Shared/TypingViews:Perm Shared/TypingViews:Nominal Shared/TypingViews:RawType Shared/TypingViews:ValueType.whole
:uses: given.typing.views

A *permission* \\(\pi\\) describes unique or shared access. A *nominal type*
\\(N\\) pairs a class name \\(C\\) with a
[signed view](given-typing.md#claim-given.typing.views) \\(A\\).
A *type* \\(T\\) may apply a permission to another type:

\\[
\begin{aligned}
\pi &::= \mathsf{given}\mid\mathsf{shared},\\
N &::= C.A,\\
T &::= N\mid\pi\,T.
\end{aligned}
\\]

Bare \\(C\\) still abbreviates \\(C.\{\epsilon\}\\). Positive view entries
expose initialized subtrees; negative entries describe empty slots; omitted
branches are unknown and inaccessible. Views do not assign ownership modes
to objects.
```

```{definition} shared.typing.composition
:lean: Shared/TypingViews:Perm.comp
:uses: shared.typing.types

*Permission composition* \\(\pi\pi'\\) combines an outer [permission](#claim-shared.typing.types) with an
inner one. The result is `given` only when both are `given`:

| Outer permission | Inner `given` | Inner `shared` |
| --- | --- | --- |
| `given` | `given` | `shared` |
| `shared` | `shared` | `shared` |
```

```{definition} shared.typing.normalization
:lean: Shared/TypingViews:ValueType Shared/TypingViews:RawType.normalize Shared/TypingViews:normalize Shared/TypingViews:Normalized
:uses: shared.typing.types shared.typing.composition given.typing.normalization

*Type normalization* combines nested permissions and normalizes the nominal
view. Its *normalized form* has exactly one outer permission:

\\[
\pi\,C.A.
\\]

Combine permissions using [composition](#claim-shared.typing.composition)
and these equations:

\\[
\mathsf{given}\ T=T,
\qquad
\pi(\pi'T)=(\href{#claim-shared.typing.composition}{\pi\pi'})T.
\\]

Normalize the nominal view using
[Given's view normalization](given-typing.md#claim-given.typing.normalization).
A bare nominal type supplies the outer permission `given`; we omit that
permission when printing. Thus `shared shared Token` normalizes to
`shared Token`.
```

```{definition} shared.typing.perm
:lean: Shared/TypingViews:ValueType.perm
:uses: shared.typing.normalization

The *permission of a type* \\(\operatorname{perm}(T)\\) is its outer permission
in [normalized form](#claim-shared.typing.normalization):

\\[
\operatorname{perm}(\pi\,C.A)=\pi.
\\]

A type printed without a permission has permission `given`.
```

```{definition} shared.typing.base
:lean: Shared/TypingViews:ValueType.base
:uses: shared.typing.normalization

The *base class* \\(\operatorname{base}(T)\\) is the class named by a type,
independent of its permission and view. For a
[normalized type](#claim-shared.typing.normalization):

\\[
\operatorname{base}(\pi\,C.A)=C.
\\]
```

```{definition} shared.typing.declarations
:lean: Shared/TypingViews:FieldType Shared/TypingViews:FieldType.toType Shared/TypingViews:TypedClass Shared/TypingViews:ClassTable
:uses: shared.typing.types given.typing.declarations

A *typed class table* \\(\Sigma\\) gives each field a [permission and a class](#claim-shared.typing.types).
Constructor arguments must supply whole values of the declared types:

\\[
\begin{aligned}
F &::= \pi\,C,\\
d &::= \mathsf{class}\ C\ \{f_1:F_1,\ldots,f_n:F_n\},\\
\Sigma &\in \mathsf{ClassName}\rightharpoonup
  \mathsf{List}(\mathsf{FieldName}\times F).
\end{aligned}
\\]

Here \\(F\\) also denotes the set of field types generated by its grammar.
```

```{definition} shared.typing.well_formed_classes
:lean: Shared/TypingViews:ClassTable.WellFormed
:uses: shared.typing.declarations

A [typed class table](#claim-shared.typing.declarations) \\(\Sigma\\) is *well formed* when class names are
distinct, field names within each class are distinct, and every class named
by a field type is declared in \\(\Sigma\\).
```

```{definition} shared.typing.erasure
:lean: Shared/TypingViews:ClassTable.erase
:uses: shared.typing.declarations shared.syntax shared.programs

*Class-table erasure* \\(\lfloor\Sigma\rfloor\\) supplies the
[operational class table](shared.md#claim-shared.programs) by removing field
types. It retains every class name and the order of its fields:

\\[
\lfloor\Sigma\rfloor(C)=[f_1,\ldots,f_n]
\quad\text{where }\href{#claim-shared.typing.declarations}{\Sigma(C)}=[f_1:F_1,\ldots,f_n:F_n].
\\]
```

```{definition} shared.typing.nominal_table
:lean: Shared/TypingViews:ClassTable.nominal
:uses: shared.typing.declarations given.typing.declarations given.typing.views given.typing.normalization given.typing.focus given.typing.emptying given.typing.paths

The *nominal class table* \\(\Sigma_{\mathrm{nom}}\\) supplies
[Given's typed class table](given-typing.md#claim-given.typing.declarations)
by removing each field's permission and retaining its class:

\\[
\Sigma_{\mathrm{nom}}(C)=[f_1:C_1,\ldots,f_n:C_n]
\quad\text{where }\href{#claim-shared.typing.declarations}{\Sigma(C)}=[f_1:\pi_1 C_1,\ldots,f_n:\pi_n C_n].
\\]

Use this table for Given's [relative paths](given-typing.md#claim-given.typing.paths) and
[views](given-typing.md#claim-given.typing.views),
[view normalization](given-typing.md#claim-given.typing.normalization),
[nominal focusing](given-typing.md#claim-given.typing.focus), and
[emptying](given-typing.md#claim-given.typing.emptying).
```

```{definition} shared.typing.well_formed_types
:lean: Shared/TypingViews:ValueType.WellFormed
:uses: shared.typing.base shared.typing.nominal_table given.typing.views given.typing.well_formed_types

A type is *well formed* when its [base class](#claim-shared.typing.base) is
declared and its view satisfies
[Given's view conditions](given-typing.md#claim-given.typing.well_formed_types) under
the [nominal class table](#claim-shared.typing.nominal_table): paths are valid,
distinct, and pairwise prefix-incomparable.
```

```{definition} shared.typing.observations
:lean: Shared/TypingViews:Pos Shared/TypingViews:Neg
:uses: shared.typing.normalization shared.typing.nominal_table given.typing.observations

The *known-initialized paths* \\(\operatorname{pos}_{\Sigma}(T)\\) and
*known-empty paths* \\(\operatorname{neg}_{\Sigma}(T)\\) depend on a type's
nominal view, not its permission. For [normalized](#claim-shared.typing.normalization) \\(T=\pi N\\), use
[Given's observations](given-typing.md#claim-given.typing.observations) under
the [nominal class table](#claim-shared.typing.nominal_table):

\\[
\operatorname{pos}_{\Sigma}(\pi N)=\href{given-typing.html#claim-given.typing.observations}{\operatorname{pos}}_{\href{#claim-shared.typing.nominal_table}{\Sigma_{\mathrm{nom}}}}(N),
\qquad
\operatorname{neg}_{\Sigma}(\pi N)=\href{given-typing.html#claim-given.typing.observations}{\operatorname{neg}}_{\href{#claim-shared.typing.nominal_table}{\Sigma_{\mathrm{nom}}}}(N).
\\]

A positive entry exposes a whole declared subtree, including shared fields.
A negative entry describes an empty slot; an omitted branch remains unknown
and inaccessible.
```

## Following a path

````{example} shared.typing.example.paths
:lean: Shared/TypingChecks:permission_paths
:uses: shared.typing.declarations shared.resolution shared.typing.composition

With [permission composition](#claim-shared.typing.composition), a shared link
may occur anywhere along a path:

```dada
class Token {}
class Box { item: Token }
class Outer { box: shared Box }
class Holder { item: shared Token }
```

Consider initialized variables `b: Box`, `s: shared Box`, `o: Outer`, and
`h: Holder`:

| Place | Effective type | Giving it |
| --- | --- | --- |
| `b.item` | `Token` | Moves the token. |
| `s.item` | `shared Token` | Copies a shared reference. |
| `o.box.item` | `shared Token` | Copies a shared reference. |
| `h.item` | `shared Token` | Copies a shared reference. |

In the third row, `o` is unique but its `box` field is shared. In the fourth,
the final field itself is declared shared. A unique container can therefore
contain a field that is copied when given.
````

```{definition} shared.typing.declared_permission
:lean: Shared/TypingViews:declaredPermission
:uses: shared.typing.declarations shared.typing.composition shared.typing.nominal_table given.typing.views given.typing.paths given.typing.class_at

The *declared permission* \\(\operatorname{decl}_{\Sigma}(C,\rho)\\)
combines the field permissions along a [relative path](given-typing.md#claim-given.typing.paths) \\(\rho\\) from class
\\(C\\), using [permission composition](#claim-shared.typing.composition):

\\[
\begin{aligned}
\operatorname{decl}_{\Sigma}(C,\epsilon)&=\mathsf{given},\\
\operatorname{decl}_{\Sigma}(C,f\rho)&=
  \pi_f\operatorname{decl}_{\Sigma}(D,\rho)
  &&\text{where }(f:\pi_f D)\in\href{#claim-shared.typing.declarations}{\Sigma(C)}.
\end{aligned}
\\]

It is defined exactly on [paths valid from](given-typing.md#claim-given.typing.class_at)
\\(C\\) under the [nominal class table](#claim-shared.typing.nominal_table).
```

```{definition} shared.typing.focus
:lean: Shared/TypingViews:focus
:uses: shared.typing.declared_permission shared.typing.nominal_table shared.typing.observations given.typing.focus shared.typing.example.paths shared.typing.types shared.typing.normalization given.typing.views shared.typing.declarations shared.typing.composition

*Focusing* \\(T\downarrow\rho\\) finds the type reached by a path, carrying
the enclosing permission into each field. Access to a field [declared](#claim-shared.typing.declarations)
\\(F\\) through a whole value of type \\(\pi\,C\\) has type \\(\pi F\\).

Using [permission composition](#claim-shared.typing.composition), extend
[Given's focusing operation](given-typing.md#claim-given.typing.focus)
(\\(\href{given-typing.html#claim-given.typing.focus}{N\downarrow\rho}\\)) to a
[type](#claim-shared.typing.types) \\(T=\pi N\\), where the
[nominal type](#claim-shared.typing.types) is \\(N=C.A\\):

\\[
T\downarrow\rho
=\bigl(\pi\href{#claim-shared.typing.declared_permission}{\operatorname{decl}_{\Sigma}(C,\rho)}\bigr)
  (\href{given-typing.html#claim-given.typing.focus}{N\downarrow\rho}),
\qquad \rho\in\href{#claim-shared.typing.observations}{\operatorname{pos}_{\Sigma}(T)}.
\\]

The nominal focus uses the [nominal class table](#claim-shared.typing.nominal_table)
and preserves the field's current view, including holes. The new operation
\\(T\downarrow\rho\\) adds the effective permission
and [normalizes the result](#claim-shared.typing.normalization).
It does not restore moved or hidden fields.
```

```{definition} shared.typing.emptying
:lean: Shared/TypingViews:emptyPath
:uses: shared.typing.normalization shared.typing.observations shared.typing.nominal_table given.typing.emptying

*Emptying* \\(T[-\rho]\\) marks a field path as empty while retaining the
outer permission and every other branch's information. For [normalized](#claim-shared.typing.normalization)
\\(T=\pi N\\):

\\[
(\pi N)[-\rho]=\pi\,(\href{given-typing.html#claim-given.typing.emptying}{N[-\rho]}),
\qquad \rho\ne\epsilon,\quad
\rho\in\href{#claim-shared.typing.observations}{\operatorname{pos}_{\Sigma}(T)}.
\\]

The right-hand side uses [Given's emptying operation](given-typing.md#claim-given.typing.emptying)
under the [nominal class table](#claim-shared.typing.nominal_table).
[Normalize](#claim-shared.typing.normalization) the result.
```

## The static give operation

```{definition} shared.typing.environments
:lean: Shared/Typing:SlotDescription Shared/Typing:Environment Shared/Typing:Environment.WellFormed Shared/Typing:Environment.lookup Shared/Typing:Environment.replace
:uses: shared.typing.types shared.typing.well_formed_types shared.typing.normalization given.typing.environments

A *slot description* \\(B\\) is either \\(0\\), for an empty variable, or
a type. A *typing environment* \\(\Gamma\\) describes every variable slot:

\\[
B::=0\mid T,
\qquad
\Gamma\in\mathsf{VariableId}\rightharpoonup B.
\\]

Types must be [well formed](#claim-shared.typing.well_formed_types) and
[normalized](#claim-shared.typing.normalization). Empty variables remain in
the domain and cannot be reused as fresh names.
```

```{definition} shared.typing.giving
:lean: Shared/Typing:splitPlace Shared/Typing:give
:uses: shared.typing.environments shared.typing.perm shared.typing.focus shared.typing.observations shared.typing.emptying shared.syntax given.typing.paths

The *static give operation* computes the type produced by giving a place and
the [environment](#claim-shared.typing.environments) afterwards. Write
\\(\mathsf{give}_{\Sigma}(\Gamma,p)=(T,\Gamma')\\): the result has type \\(T\\),
and the variable slots have descriptions \\(\Gamma'\\).

Write a [place](shared.md#claim-shared.syntax) as \\(p=x.\rho\\): for `o.box.item`, the root variable is `o`
and the [relative path](given-typing.md#claim-given.typing.paths) is `box.item`; for `o`, the relative path is
\\(\epsilon\\). The operation is defined exactly when \\(\Gamma(x)=U\\)
and \\(\rho\in\href{#claim-shared.typing.observations}{\operatorname{pos}_{\Sigma}(U)}\\). Its outputs are:

\\[
T=\href{#claim-shared.typing.focus}{U\downarrow\rho},
\qquad
\Gamma'=\begin{cases}
\Gamma & \href{#claim-shared.typing.perm}{\operatorname{perm}(T)}=\mathsf{shared},\\
\Gamma[x\mapsto0] & \href{#claim-shared.typing.perm}{\operatorname{perm}(T)}=\mathsf{given},\ \rho=\epsilon,\\
\Gamma[x\mapsto \href{#claim-shared.typing.emptying}{U[-\rho]}] & \href{#claim-shared.typing.perm}{\operatorname{perm}(T)}=\mathsf{given},\ \rho\ne\epsilon.
\end{cases}
\\]

The last case [empties the field path](#claim-shared.typing.emptying).
A given result requires every permission along
its route to be given. A shared result leaves the entire environment unchanged.
An absent variable, an empty source, or an inaccessible field makes this static
give operation undefined. A field hidden by a view may still hold a value at runtime.
```

## Weakening a view

```{definition} shared.typing.weakening
:lean: Shared/TypingViews:Subtype
:uses: shared.typing.normalization shared.typing.observations given.typing.forgetting shared.evaluation

As in [Given](given-typing.md#claim-given.typing.forgetting), view weakening
can hide initialization facts while preserving the permission.
For [normalized types](#claim-shared.typing.normalization)
\\(T=\pi C.A\\) and \\(U=\pi'C'.A'\\), define:

\\[
T\preceq_{\Sigma}U
\iff
\begin{gathered}
\pi=\pi'\ \land\ C=C'\\
{}\land\ \href{#claim-shared.typing.observations}{\operatorname{pos}_{\Sigma}(U)}\subseteq\href{#claim-shared.typing.observations}{\operatorname{pos}_{\Sigma}(T)}\\
{}\land\ \href{#claim-shared.typing.observations}{\operatorname{neg}_{\Sigma}(U)}\subseteq\href{#claim-shared.typing.observations}{\operatorname{neg}_{\Sigma}(T)}.
\end{gathered}
\\]

For example, `shared Box` can be weakened to `shared Box.{}`. There is no
weakening from `Box` to `shared Box`: creating a shared reference requires the
runtime [give-share operation](shared.md#claim-shared.evaluation). Different aliases may expose different views
of the same object.
```

## Typing expressions

```{definition} shared.typing.expressions
:lean: Shared/Typing:ExprTyped Shared/Typing:ArgsTyped
:uses: shared.typing.giving shared.typing.weakening shared.typing.declarations shared.syntax shared.typing.normalization

*Expression typing* \\(\Sigma;\Gamma\vdash e:T\;\triangleright\;\Gamma'\\)
records the result's type and the variable descriptions after evaluation.
All type expressions in the rules use
[type normalization](#claim-shared.typing.normalization).
Both Give and Give-share use the
[static give operation](#claim-shared.typing.giving)
\\(\href{#claim-shared.typing.giving}{\mathsf{give}_{\Sigma}(\Gamma,p)=(T,\Gamma')}\\) defined above.
Give returns its result type; Give-share applies `shared` to that type:

\\[
\frac{\href{#claim-shared.typing.giving}{\mathsf{give}_{\Sigma}(\Gamma,p)=(T,\Gamma')}}
{\Sigma;\Gamma\vdash p\mathord{\to}:T\;\triangleright\;\Gamma'}
\quad\text{Give}
\\]

\\[
\frac{\href{#claim-shared.typing.giving}{\mathsf{give}_{\Sigma}(\Gamma,p)=(T,\Gamma')}}
{\Sigma;\Gamma\vdash p\mathord{\to}\mathsf{share}:\mathsf{shared}\ T
  \;\triangleright\;\Gamma'}
\quad\text{Give-share}
\\]

Both rules make the same change to the source. Give-share preserves the result's
view: it changes permission, not initialization.

**Construct** checks arguments from left to right against the declared field
types. The new object's reference is given, even when some fields are shared:

\\[
\frac{
\begin{gathered}
\href{#claim-shared.typing.declarations}{\Sigma(C)}=[f_1:F_1,\ldots,f_n:F_n]\\
\Sigma;\Gamma_{i-1}\vdash e_i:F_i\;\triangleright\;\Gamma_i
  \quad(1\le i\le n)
\end{gathered}
}{
\Sigma;\Gamma_0\vdash\mathsf{new}\ C(e_1,\ldots,e_n):C
  \;\triangleright\;\Gamma_n
}
\quad\text{Construct}
\\]

The argument count must match the declaration. With no arguments, the
environment is unchanged. Arguments still require their whole declared types.
A result may expose a [weaker view](#claim-shared.typing.weakening):

\\[
\frac{\Sigma;\Gamma\vdash e:T\;\triangleright\;\Gamma'
  \qquad\href{#claim-shared.typing.weakening}{T\preceq_{\Sigma}U}}
{\Sigma;\Gamma\vdash e:U\;\triangleright\;\Gamma'}
\quad\text{Weaken}
\\]
```

````{example} shared.typing.example.arguments
:lean: Shared/TypingExecutionChecks:constructor_permissions
:uses: shared.typing.example.paths shared.typing.expressions

With `Token`, `Box`, and `Holder` [declared above](#claim-shared.typing.example.paths):

```dada
let t = new Token();
let h = new Holder(t→share);
let a = h.item→;
let b = h.item→;
```

The [constructor rule](#claim-shared.typing.expressions) requires a `shared Token`, so its argument explicitly shares
the token. Afterwards `t` is empty, `h: Holder`, and both `a` and `b` have
type `shared Token`. Giving `h.item` does not empty it.

Replacing the constructor argument with `t→` is rejected: its type is `Token`,
not the declared `shared Token`. Conversely, `new Box(a→)` is rejected because
the shared result cannot supply the given `Token` required by `Box`.
````

````{example} shared.typing.example.partial
:lean: Shared/TypingExecutionChecks:sharing_partial_views
:uses: shared.typing.expressions given.typing.example.views shared.typing.weakening

Sharing also preserves a partially moved value:

```dada
class Token {}
class Pair { left: Token, right: Token }

let p = new Pair(new Token(), new Token());
let t = p.left→;
let s = p→share;
let a = s.right→;
let b = s.right→;
```

Moving `left` leaves `p: Pair.{-left, right}`. [Give-share](#claim-shared.typing.expressions) then empties `p` and
produces `s: shared Pair.{-left, right}`. The last two statements produce
shared tokens and preserve that view of `s`.

Giving `s.left→` is rejected because `left` is empty.
[Weakening](#claim-shared.typing.weakening) `s`'s view could hide that fact, but
could not make the field accessible again.
````

## Binding results

```{definition} shared.typing.patterns
:lean: Shared/Unpacking:Pattern Shared/Unpacking:Statement
:uses: given.patterns

An unpacking pattern consumes a uniquely owned container and transfers its
field slots to fresh variables. This extends Shared's statements with
[Given's flat *binding patterns*](given.md#claim-given.patterns) \\(b\\):

\\[
\begin{aligned}
b&::=x\mid C\mathord{\to}\{f_1:x_1,\ldots,f_n:x_n\},\\
t&::=\mathsf{let}\ b=e.
\end{aligned}
\\]

Each declared field must appear exactly once; destination variables are distinct
and fresh in the variable table after expression evaluation. Field order in the
pattern is immaterial. `f` abbreviates `f: f`;
there are no `_` or `..` patterns here.
```

```{definition} shared.typing.machine
:lean: Shared/Unpacking:Configuration
:uses: shared.typing.patterns shared.state

A *configuration* \\(K=\langle S,P\rangle\\) pairs [storage](shared.md#claim-shared.state) with the remaining
[statements](#claim-shared.typing.patterns).
```

```{definition} shared.typing.steps
:lean: Shared/Unpacking:Transfer Shared/Unpacking:Bind Shared/Unpacking:Step
:uses: shared.typing.machine shared.typing.patterns given.unpacking shared.evaluation shared.state shared.allocated

An *extended statement step*
\\(\Delta\vdash K\longrightarrow_u K'\\) changes a [configuration](#claim-shared.typing.machine) by running one `let` statement with a
[binding pattern](#claim-shared.typing.patterns).

Write \\(\href{shared.html#claim-shared.evaluation}{\Delta\vdash\langle S,e\rangle\Downarrow\langle S',r\rangle}\\)
for [Shared's expression evaluation](shared.md#claim-shared.evaluation). It is
unchanged. The extended step first evaluates the expression, then binds its result:

- A variable pattern stores the reference, of either mode, in its fresh slot.
- A `C → { ... }` pattern requires \\(r=(\mathsf{unique},\alpha)\\) and
  an [allocated](shared.md#claim-shared.allocated) `C` object at \\(\alpha\\). Transfer every field slot to its
  named destination and remove \\(\alpha\\) from the object table.

Field references retain their modes and targets; empty fields become empty
variables. All other storage and the allocation counter remain as in
\\(S'\\). The statement is removed from the remaining sequence. A shared
result has no unpacking transition: consuming its container would invalidate
other owners. This is an extension of the preceding chapter's machine.
```

```{definition} shared.typing.execution
:lean: Shared/Unpacking:Steps
:uses: shared.typing.steps

A *finite execution* \\(\Delta\vdash K\longrightarrow_u^{*}K'\\) consists
of zero or more [extended statement steps](#claim-shared.typing.steps), all
using the same class table \\(\Delta\\).
```

```{definition} shared.typing.finished
:lean: Shared/Unpacking:Configuration.finished
:uses: shared.typing.machine

A [configuration](#claim-shared.typing.machine) is *finished* when no statements remain:

\\[
\mathsf{Finished}(\langle S,P\rangle)\iff P=[].
\\]
```

```{definition} shared.typing.outcomes
:lean: Shared/Unpacking:Stuck
:uses: shared.typing.machine shared.typing.steps

A [configuration](#claim-shared.typing.machine) is *stuck* when statements remain but no
[extended step](#claim-shared.typing.steps) is possible:

\\[
\mathsf{Stuck}_{\Delta}(\langle S,P\rangle)\iff
  P\ne[]\ \land\ \neg\exists K'.\;\href{#claim-shared.typing.steps}{\Delta\vdash\langle S,P\rangle\longrightarrow_u K'}.
\\]
```

```{definition} shared.typing.field
:lean: Shared/Typing:fieldDescription
:uses: shared.typing.environments shared.typing.focus shared.typing.observations shared.typing.patterns

The *field description* \\(\mathsf{field}_{\Sigma}(T,f)\\) tells an [unpacking
pattern](#claim-shared.typing.patterns) whether a direct field is empty or which type it transfers:

\\[
\mathsf{field}_{\Sigma}(T,f)=\begin{cases}
0&f\in\href{#claim-shared.typing.observations}{\operatorname{neg}_{\Sigma}(T)},\\
\href{#claim-shared.typing.focus}{T\downarrow f}&f\in\href{#claim-shared.typing.observations}{\operatorname{pos}_{\Sigma}(T)}.
\end{cases}
\\]

An unknown field has no description.
```

```{definition} shared.typing.bindings
:lean: Shared/Typing:FieldBindings Shared/Typing:BindingTyped
:uses: shared.typing.patterns shared.typing.environments shared.typing.field shared.typing.perm shared.typing.base shared.typing.declarations given.typing.bindings

*Binding typing* \\(\Sigma;\Gamma\vdash b:T\Rightarrow\Gamma'\\) describes
where a result goes in the [environment](#claim-shared.typing.environments). A fresh variable receives its type unchanged:

\\[
\frac{x\notin\operatorname{dom}(\Gamma)}
{\Sigma;\Gamma\vdash x:T\Rightarrow\Gamma[x\mapsto T]}
\quad\text{Bind}
\\]

For unpacking, the container must be given and every direct field's status
must be known. Unpacking transfers its
[field descriptions](#claim-shared.typing.field):

\\[
\frac{
\begin{gathered}
\href{#claim-shared.typing.perm}{\operatorname{perm}(T)}=\mathsf{given}
\qquad\href{#claim-shared.typing.base}{\operatorname{base}(T)}=C
\qquad\href{#claim-shared.typing.declarations}{\Sigma(C)}=[f_1:F_1,\ldots,f_n:F_n]\\
\href{#claim-shared.typing.field}{\mathsf{field}_{\Sigma}(T,f_i)}=B_i\quad(1\le i\le n)\\
x_1,\ldots,x_n\text{ distinct and absent from }\operatorname{dom}(\Gamma)
\end{gathered}
}{
\Sigma;\Gamma\vdash C\mathord{\to}\{f_1:x_1,\ldots,f_n:x_n\}:T
  \Rightarrow\Gamma[x_1\mapsto B_1,\ldots,x_n\mapsto B_n]
}
\quad\text{Unpack}
\\]

The displayed fields are ordered as declared. A transferred field can be
shared even though the container must be given. As in
[Given's binding rules](given-typing.md#claim-given.typing.bindings), a field's
interior may have a partial view; only its direct slot status must be known.
```

````{example} shared.typing.example.unpack
:lean: Shared/TypingExecutionChecks:unpacking_shared_fields
:uses: shared.typing.bindings shared.typing.example.arguments

Continuing the [`Holder` example](#claim-shared.typing.example.arguments):

```dada
let Holder → { item } = h→;
let c = item→;
```

The [unpacking rule](#claim-shared.typing.bindings) empties `h`, consumes the holder, and binds
`item: shared Token`. The aliases `a` and `b` still own the token. The second
copies it again, leaving `item` initialized.

If `s: shared Holder`, the pattern `let Holder → { item } = s→` is rejected.
The result is shared even if this happens to be the only reference to that
holder. A type grants the access its permission describes; it does not count
aliases to recover unique ownership.
````

```{definition} shared.typing.statements
:lean: Shared/Typing:StatementTyped
:uses: shared.typing.expressions shared.typing.bindings given.typing.statements

*Statement typing* \\(\Sigma;\Gamma\vdash t\Rightarrow\Gamma'\\) threads
the environment through [expression typing](#claim-shared.typing.expressions)
and [binding typing](#claim-shared.typing.bindings):

\\[
\frac{\href{#claim-shared.typing.expressions}{\Sigma;\Gamma\vdash e:T\;\triangleright\;\Gamma_1}
  \qquad\href{#claim-shared.typing.bindings}{\Sigma;\Gamma_1\vdash b:T\Rightarrow\Gamma_2}}
{\Sigma;\Gamma\vdash\mathsf{let}\ b=e\Rightarrow\Gamma_2}
\quad\text{Let}
\\]
```

```{definition} shared.typing.sequences
:lean: Shared/Typing:SequenceTyped
:uses: shared.typing.statements

*Statement-sequence typing* \\(\Sigma;\Gamma\vdash P\Rightarrow\Gamma_f\\)
passes each [statement's](#claim-shared.typing.statements) resulting
environment to the next. Here \\(P\\) is an ordered sequence of statements:

\\[
\frac{}{\Sigma;\Gamma\vdash[]\Rightarrow\Gamma}
\qquad
\frac{\href{#claim-shared.typing.statements}{\Sigma;\Gamma\vdash t\Rightarrow\Gamma_1}
  \qquad\Sigma;\Gamma_1\vdash P\Rightarrow\Gamma_f}
{\Sigma;\Gamma\vdash t::P\Rightarrow\Gamma_f}.
\\]
```

```{definition} shared.typing.programs
:lean: Shared/Typing:ProgramTyped
:uses: shared.typing.well_formed_classes shared.typing.sequences

A *well-typed program* has a
[well-formed typed class table](#claim-shared.typing.well_formed_classes) \\(\Sigma\\)
and a statement sequence \\(P\\) that
[typechecks](#claim-shared.typing.sequences) from the empty environment:

\\[
\exists\Gamma_f.\;\href{#claim-shared.typing.sequences}{\Sigma;\varnothing\vdash P\Rightarrow\Gamma_f}.
\\]

Completion retains the final storage; the final environment need not be empty.
```

## Relating types to storage

```{definition} shared.typing.mode
:lean: Shared/TypingViews:Perm.toMode
:uses: shared.typing.types shared.state shared.references

The *runtime mode* \\(\operatorname{mode}(\pi)\\) maps a [type permission](#claim-shared.typing.types) to
the corresponding [reference mode](shared.md#claim-shared.references):

\\[
\begin{aligned}
\operatorname{mode}(\mathsf{given})&=\mathsf{unique},\\
\operatorname{mode}(\mathsf{shared})&=\mathsf{shared}.
\end{aligned}
\\]
```

```{definition} shared.typing.read
:lean: Shared/TypingPaths:enter Shared/TypingPaths:readPath
:uses: shared.resolution shared.references given.typing.paths

For \\(r=(\kappa,\alpha)\\), the *reference-path read* \\(\mathsf{read}_S(r,\rho)\\) follows a [relative path](given-typing.md#claim-given.typing.paths) \\(\rho\\) from
\\(\alpha\\), accumulating reference modes starting with \\(\kappa\\),
as in {anchor-ref}`shared.resolution`. The empty path returns \\(r\\) if its object exists.
A missing object or field encountered while following the path, or an empty
intermediate slot, makes traversal undefined. The final slot may be empty;
if occupied, its reference is returned without dereferencing the target.
```

```{definition} shared.typing.reference_realization
:lean: Shared/TypingRealization:Satisfies
:uses: shared.typing.read shared.typing.observations shared.typing.declared_permission shared.typing.mode shared.typing.normalization shared.typing.composition shared.allocated given.typing.satisfaction given.typing.class_at

*Reference realization* \\(\Sigma;S\models r:T\\) says that a reference's
type describes access from that reference. It does not prescribe one view for
the object independent of its aliases.

Using the [reference-path read](#claim-shared.typing.read), the relation holds for a
[normalized type](#claim-shared.typing.normalization) \\(T=\pi C.A\\), when:

1. The root reference has mode \\(\href{#claim-shared.typing.mode}{\operatorname{mode}(\pi)}\\) and targets
   an [allocated object](shared.md#claim-shared.allocated) of class \\(C\\).
2. Every \\(\rho\in\href{#claim-shared.typing.observations}{\operatorname{pos}_{\Sigma}(T)}\\) reaches an allocated
   object of its declared class. Every \\(\rho\in\href{#claim-shared.typing.observations}{\operatorname{neg}_{\Sigma}(T)}\\)
   reaches an existing empty slot.
3. Every [valid](given-typing.md#claim-given.typing.class_at) finite [path read](#claim-shared.typing.read) from \\(C\\) that reaches an occupied slot from
   this root, including paths hidden by the view,
   has effective mode
   \\(\href{#claim-shared.typing.mode}{\operatorname{mode}}(\pi\href{#claim-shared.typing.declared_permission}{\operatorname{decl}_{\Sigma}(C,\rho)})\\).

The third condition [composes](#claim-shared.typing.composition) permissions
along the whole route. A field declared given inside a
shared container may store a unique reference before copying and a shared one
afterwards. Both routes have effective shared mode.
```

```{definition} shared.typing.realization
:lean: Shared/TypingRealization:FieldsMatchClasses Shared/TypingRealization:PendingValues Shared/TypingRealization:Realizes
:uses: shared.typing.environments shared.typing.reference_realization shared.typing.well_formed_classes shared.typing.well_formed_types shared.state shared.well_formed

*Storage realization* \\(\Sigma;\Gamma\models(S;R)\\) relates all [variables](#claim-shared.typing.environments)
and pending results to their type descriptions.

Here \\(S=\langle O,V,\nu\rangle\\) is the
[storage](shared.md#claim-shared.state), and \\(R\\) is an ordered list of
*pending values* \\((r:T)\\): expression results not yet stored by a binding
or constructor. The relation holds when:

- Structural well-formedness holds as in {anchor-ref}`shared.well_formed`,
  counting pending references alongside all stored owning occurrences.
- Every occupied field targets an object of its declared class, including
  fields hidden by views.
- \\(\operatorname{dom}(\Gamma)=\operatorname{dom}(V)\\). A description
  \\(\Gamma(x)=0\\) means \\(V(x)=\bot\\); a description \\(\Gamma(x)=T\\)
  means \\(V(x)=r\\) with
  [reference realization](#claim-shared.typing.reference_realization)
  \\(\href{#claim-shared.typing.reference_realization}{\Sigma;S\models r:T}\\).
- Every pending pair \\((r:T)\\) satisfies
  \\(\href{#claim-shared.typing.reference_realization}{\Sigma;S\models r:T}\\).

The [table](#claim-shared.typing.well_formed_classes) \\(\Sigma\\) and all
[types](#claim-shared.typing.well_formed_types) must be well formed; types must
also be [normalized](#claim-shared.typing.normalization). Shared aliases
may carry different views; each must describe the actual storage. Hidden
references still contribute to ownership and liveness.
```

```{lemma} shared.typing.expression_soundness
:lean: Shared/TypingSafety:expression_soundness
:uses: shared.typing.realization shared.typing.expressions shared.typing.well_formed_classes shared.typing.erasure shared.steps shared.evaluation

For any [well-formed](#claim-shared.typing.well_formed_classes) \\(\Sigma\\),
if [expression typing](#claim-shared.typing.expressions) and
[storage realization](#claim-shared.typing.realization) give

\\[
\href{#claim-shared.typing.expressions}{\Sigma;\Gamma\vdash e:T\;\triangleright\;\Gamma'},
\qquad\href{#claim-shared.typing.realization}{\Sigma;\Gamma\models(S;R)},
\\]

then an [evaluation](shared.md#claim-shared.evaluation) exists:

\\[
\exists S',r.\;
\href{#claim-shared.typing.erasure}{\lfloor\Sigma\rfloor}\vdash\langle S,e\rangle\href{shared.html#claim-shared.evaluation}{\Downarrow}\langle S',r\rangle.
\\]

Every such evaluation satisfies
\\(\href{#claim-shared.typing.realization}{\Sigma;\Gamma'\models(S';R\mathbin{+\!\!+}[(r:T)])}\\), where
\\(+\!\!+\\) appends lists. This includes arbitrary pending results of
earlier constructor arguments. A copy preserves existing aliases' views;
a move preserves the types of the other owning roots.
```

```{definition} shared.typing.configurations
:lean: Shared/TypedConfigurations:ConfigurationTyped
:uses: shared.typing.realization shared.typing.sequences shared.typing.steps shared.typing.well_formed_classes shared.typing.machine

A [configuration](#claim-shared.typing.machine) \\(K=\langle S,P\rangle\\)
is *well typed* with final
environment \\(\Gamma_f\\) when:

\\[
\Sigma\vdash\langle S,P\rangle:\Gamma_f
\iff
\exists\Gamma.\;
  \href{#claim-shared.typing.realization}{\Sigma;\Gamma\models(S;[])}
  \land\href{#claim-shared.typing.sequences}{\Sigma;\Gamma\vdash P\Rightarrow\Gamma_f}.
\\]

The two premises are [storage realization](#claim-shared.typing.realization)
and [statement-sequence typing](#claim-shared.typing.sequences).
The class table \\(\Sigma\\) must be
[well formed](#claim-shared.typing.well_formed_classes).
```

## Progress and preservation

```{theorem} shared.typing.progress
:lean: Shared/TypingSafety:ConfigurationTyped.progress
:uses: shared.typing.configurations shared.typing.expression_soundness shared.typing.bindings shared.typing.outcomes shared.typing.steps shared.typing.erasure shared.typing.finished

A [well-typed configuration](#claim-shared.typing.configurations) has
[finished](#claim-shared.typing.finished) or can take a
[step](#claim-shared.typing.steps):

\\[
\href{#claim-shared.typing.configurations}{\Sigma\vdash K:\Gamma_f}
\quad\Longrightarrow\quad
\href{#claim-shared.typing.finished}{\mathsf{Finished}(K)}\ \lor\
\exists K'.\;\href{#claim-shared.typing.erasure}{\lfloor\Sigma\rfloor}\vdash K\href{#claim-shared.typing.steps}{\longrightarrow_u} K'.
\\]
```

```{theorem} shared.typing.preservation
:lean: Shared/TypingSafety:ConfigurationTyped.preservation
:uses: shared.typing.configurations shared.typing.expression_soundness shared.typing.bindings shared.typing.steps shared.typing.erasure

Every [step](#claim-shared.typing.steps) from a
[well-typed configuration](#claim-shared.typing.configurations) preserves
its final typing:

\\[
\frac{\href{#claim-shared.typing.configurations}{\Sigma\vdash K:\Gamma_f}
  \qquad\href{#claim-shared.typing.erasure}{\lfloor\Sigma\rfloor}\vdash K\href{#claim-shared.typing.steps}{\longrightarrow_u} K'}
{\href{#claim-shared.typing.configurations}{\Sigma\vdash K':\Gamma_f}}.
\\]

The current environment changes when a source is moved or a result is bound.
A shared give itself preserves the environment even when the final stored
reference changes mode; binding its result then adds a fresh variable.
```

```{theorem} shared.typing.safety
:lean: Shared/TypingSafety:program_safety
:uses: shared.typing.progress shared.typing.preservation shared.typing.programs shared.typing.outcomes shared.typing.execution

A [well-typed program](#claim-shared.typing.programs), started with empty
storage, cannot reach a [stuck configuration](#claim-shared.typing.outcomes).
Every [finite execution](#claim-shared.typing.execution) can be extended to a
finished one whose total step count equals the
initial number of statements. This includes
copying, give-share, and unpacking unique containers with given or shared fields.
```

```{theorem} shared.typing.given_fragment
:lean: Correspondence/UniqueSharedTyping:given_fragment
:uses: shared.typing.statements shared.typing.sequences shared.typing.patterns shared.typing.steps shared.typing.outcomes given.typing.statements shared.embedding shared.correspondence given.unpacking shared.typing.finished

Restrict field declarations and types to `given` and omit give-share
expressions. The typing rules then agree with
[Given's rules](given-typing.md#claim-given.typing.statements), including its
[unpacking extension](given.md#claim-given.unpacking). [Embedding](shared.md#claim-shared.embedding) every runtime
reference with mode `unique` preserves and reflects
[statement transitions](#claim-shared.typing.steps) and
[completion](#claim-shared.typing.finished) in this fragment.

This extends the [earlier correspondence](shared.md#claim-shared.correspondence),
which covers only single-variable bindings, to the machines with unpacking.
```
