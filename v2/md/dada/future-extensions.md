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
