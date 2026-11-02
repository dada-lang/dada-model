# Future extensions

## Generic views

````{future-note} future.generic_views
:uses: given.typing.views given.typing.expressions

A constructor could store a value without requiring all of its fields to be
initialized. Its result type would preserve the argument's view. Consider:

```dada
class Token {}
class C { left: Token, right: Token }
class D { c: C }
```

Suppose a user-defined constructor `fn` takes a `C` and stores it in field `c`
of a new `D`. A proposed *generic view* parameter would let its signature say:

\\[
\forall V:\mathsf{View}[C].\quad
\mathsf{fn}(C.V)\to D.\{c.V\}.
\\]

Here \\(V\\) ranges over views of \\(C\\). The proposed notation \\(c.V\\) carries
that view into the result's field \\(c\\). For example, an argument of type
`C.{-left, right}` would produce `D.{-c.left, c.right}`: the moved-out field
stays empty, and the other field stays accessible.

This is a future extension. The current Construct rule requires whole declared
argument types; it has neither user-defined constructors nor view parameters.

The notation must also preserve the presence of the stored object. If
\\(V=\{\}\\), the argument is an existing `C` whose fields are hidden. Simply
prefixing every entry of this empty view would produce no entries and forget
that `c` is initialized. A generic-view design must express that distinction.
The operators and their typing rules remain to be defined.
````

## Permissions that name places

````{future-note} future.path_permissions
:uses: shared.give shared.resolution given.typing.views

A later permission `given[p₁, …, pₙ]` would describe access derived from named
places. These are paths rooted at bindings, such as `x.item`, whereas a view's
paths are relative to the described object. Plain `given` abbreviates
`given[]`, the owning permission.

The permission of a named place matters. For example, these proposed function
signatures should be equivalent:

```dada
fn foo(x: shared Point) -> given[x] Point
fn foo(x: shared Point) -> shared Point
```

Because `x` provides shared ownership, deriving access from it produces shared
ownership. Simplification therefore consults the typing environment, including
the effective permission of a field path. It cannot inspect the permission
expression alone.

Permission application should retain the identity and shared-absorption laws.
For a permission \\(P\\) and a type \\(T\\), the intended equations include:

\\[
\begin{aligned}
\mathsf{given}\;P&\equiv P,
&\mathsf{given}\;T&\equiv T,\\
P\;\mathsf{shared}&\equiv\mathsf{shared},
&P\;(\mathsf{shared}\;T)&\equiv\mathsf{shared}\;T.
\end{aligned}
\\]

The meaning of multiple named places, their composition with other permissions,
and their interaction with borrowing remain to be specified. The initial Shared
type system uses only `given` and `shared`; it has no permissions that name places.
````

## Permission and type unions

````{future-note} future.permission_unions
:uses: future.path_permissions shared.give given.typing.environments

A result may have different ownership permissions on different branches.
Consider this intended use of `given[x, y]`:

```dada
fn foo(x: shared Point, y: Point) -> given[x, y] Point {
    if something { x→ } else { y→ }
}

let r = foo(a, b);
let q = r→;
```

The function and branch syntax illustrate a future language. They are not
part of the current straight-line fragments.

If `foo` returns from `x`, `r` contains a shared reference and `r→` copies it.
If it returns from `y`, `r` contains a given reference and `r→` moves it.
The machine can inspect the runtime reference; the type checker must account
for both possibilities. Simplifying this result to an always-shared type would
lose the second case.

Develop these permissions together with *permission unions* `P | Q` and *type
unions* `T | U`, revisiting the union forms in the v1 model. The design needs to
settle how alternative sources relate to combined dependencies, how unions
compose with permissions and views, and how these rules extend to leased and
shared borrowing types. The notation alone does not settle those choices.

Initialization tracking also needs a distinction between an empty slot and
one that can no longer be used. After the final give above, using `r` again is
unsafe in the given case, but claiming that its slot is empty is false in the
shared case. Given's current variable marker `0` means *known empty*. This
extension must describe the uncertainty without changing that fact silently.
````
