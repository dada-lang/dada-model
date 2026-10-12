# Surface syntax and core judgments

Programs enter through `surface::parse_program`: the surface parser constructs an
AST, desugaring judgments lower it to core, and the core checker and interpreter
operate on that result. Every program assertion helper follows this path,
including interpreter-only tests that deliberately skip checking.

The two grammars share concrete permissions and places. Surface declarations,
expressions, types, and binders have their own ASTs. Lowering walks those terms
structurally; it does not print text and parse it again.

## Permission spelling

| Surface spelling | Meaning |
| --- | --- |
| `given Data`, `given[] Data`, `[] Data` | Independent unique ownership of named `Data` |
| `given[x, y] T`, `[x, y] T` | Permission derived from the listed places |
| `shared T`, `shared[] T` | Independent shared ownership |
| `shared[x, y] T` | Sharing from the listed places |
| `![x, y] T` | Mutable access from the listed places |

The surface type shorthand `[places] T` lowers to `given[places] T`.
With nonempty origins, this permission derives its capabilities from the origin
types; it does not necessarily imply uniqueness or ownership. The annotation
describes a type and does not move a value. Empty origins instead give the
independent permission: `[] T` lowers to `given T`.

Empty mutable origins are invalid. Bare `!T` in a function parameter instead
introduces a fresh permission variable constrained by `is mut`.

## Classes, structs, and predicates

`class` declares uniquely tracked data that may have a destructor. `struct`
declares shareable data, and `shared struct` declares value data that is copyable
when its generic arguments are shared (including the case with no arguments).
Structs cannot have nonempty destructor bodies.

The predicates `unique` and `shared` describe exclusivity and duplication;
`owned` describes independence from borrowed origins. Unique ownership is the
conjunction `P is unique, P is owned`. The shareability predicate is `T is struct`.
`given` names a permission, not a declaration category or predicate: use `class`
for affine declarations and the two constraints above for unique ownership.
`mut` and `boxed` retain their separate meanings.

## Parameter defaults

Only the outermost permission of an input is implicit. When `Data` names a
class or struct, `x: Data` means `x: any Data`; each occurrence introduces its
own fresh permission variable. A bare type variable is different: `x: T`
means `x: given T` and introduces no permission binder. Here `given` is the
identity permission: it preserves the full type supplied for `T`, including
that type's permission. This applies to method type parameters, including those
declared inline, and enclosing class type parameters. Write `x: any T` to
introduce a separate permission variable, or `x: !T` to introduce one constrained
by `is mut`.

Explicit permissions such as `given Data`,
`P Data`, `[source] Data`, and `[] Data` keep their stated meaning and introduce
no permission binder. In particular, `x: [] Data` explicitly requires ownership.

For a parameter `x: Array[Data]`, only the permission on `Array` is introduced.
The element type remains owned. Field types, return types, local annotations,
and nested type arguments retain the identity default `given`. To require
ownership of a named input type explicitly, write `x: given Data`.

### Inline type declarations

An input `value: type T` declares a method type parameter `T` and uses it as the
input type. It introduces one type argument at calls, with no separate
permission argument. This surface declaration:

{anchor}`surface_inline_type_example`

lowers to this core declaration:

{anchor}`core_inline_type_example`

The receiver's generated permission comes first, followed by the inline type
parameter. These snippets are checked together by an `assert_desugars!` test.

The new type parameter is in scope throughout the method signature and body,
including earlier inputs, the return type, and `where` clauses. It may shadow
a type parameter of the enclosing class. An inline declaration cannot reuse
another method generic's name: two inline declarations of `T`, or an inline
`T` alongside an explicit method generic named `T`, are rejected.

Inline type declarations are supported only as direct inputs. Forms such as
`any type T`, `!type T`, and `Array[type T]` do not introduce binders, nor do return
types, fields, or local annotations. Once declared, `T` can appear
inside other types or use ordinary input sugar such as `any T` and `!T`.
Core keeps all type parameters in the explicit generic list.

### Receiver declarations

Surface declarations can put the receiver before the method name:

| Declaration form | Receiver permission |
| --- | --- |
| `fn self.foo(...)` | A fresh permission variable |
| `fn self!foo(...)` | A fresh permission variable constrained by `is mut` |
| `fn self->foo(...)` | Explicit `given`, with no new permission binder |

The receiver is omitted from the parentheses in these forms. Explicit generics
follow the method name, as in `fn self!foo[type T](value: T)`.

Both grammars also accept an explicit permission and `self` as the first
parameter: `fn foo(given self, ...)` or `fn foo[perm P](P self, ...)`.
Other explicit permissions, such as `shared self`, `given[x] self`, and
`![x] self`, use the same form. Core requires this explicit receiver form.
The former parameter-list receivers `self`, `any self`, `self!`, and `self->`
are rejected.

The declaration `fn self.foo(...)` is permission-generic. A call through
`value.foo[...](...)` shares the receiver place; the declaration prefix does
not fix the receiver permission to sharing.

For example, this surface declaration:

{anchor}`surface_generic_permission_example`

has the following explicit core signature (fresh names are illustrative):

{anchor}`core_generic_permission_example`

These snippets are the two sides of an `assert_desugars!` test. It lowers the
surface program and compares its AST with the independently parsed core program,
ignoring bound-variable names. This checks the expansion itself; type checking
and interpretation have separate tests.

## Calls supply all generic arguments

There is no generic argument inference. All explicitly declared generics come
first. The generated suffix starts with the receiver permission, if any, then
visits inputs from left to right, interleaving inline type parameters and generated
permission parameters. A bare type-variable input adds no permission slot, and
an explicit permission adds none either. Thus
`fn self!mix[type A](left: type T, data: Data, right: type U)` takes generic arguments
for `A`, the receiver permission, `T`, the permission on `data`, and `U`, in that
order. Calls must supply every argument, including the generated suffix:

{anchor}`explicit_generated_permission_call`

The checker resolves the actual method before checking argument count and kinds.
An incorrect list reports the expanded signature and associates generic slots
with the receiver or inputs that use them. The entry method has no caller-supplied
generic arguments, so its receiver is explicitly owned: `fn main(given self)`,
or the equivalent surface form `fn self->main()`.
Place origins written in call arguments belong to the caller, even when the
callee uses the same names for its receiver, inputs, or locals.

Surface method calls may omit the dot after a place's `!` or `->` access.
For example, `vec!push[![vec]](value)` lowers to
`vec!.push[![vec]](value)`, and `vec->iter[given]()` lowers to
`vec->.iter[given]()`. Both spellings are accepted in surface; core keeps the
dotted form. This changes only call spelling: all generic arguments are still
explicit. The receiver must be a place, including a projected place such as
`vec.field[0]`; calls on other expressions continue to use a dot.

## Tuple expressions

Both grammars separate tuple elements with commas, as in `(x, y)`, and allow a
trailing comma. `()` is unit. Both `(x)` and `(x,)` are singleton tuples;
parentheses do not introduce a grouping expression.

In surface, `(vec!, iter, ())` has three separate elements, while
`(vec!iter(),)` has one element: a method call using `vec!` as its receiver.

## Places and values

A bare `place` or `place.share` shares from that place. `place->` gives its value;
`place!` creates a mutable lease. `place->.share` first gives, then shares the value
independently. The outer independent permission does not erase dependencies in
nested field or element types. `drop place;` is a statement; it cannot be used
where an expression is required.

Value sharing keeps its dot: write `place->.share`. `share` is an operation,
not a callable method, so `place->share()` and `place->.share()` are invalid.

Core is the explicit language used by the judgments. Its source renderer emits
explicit receiver permissions, named generic binders, and dotted calls.
Named input types have explicit permissions; bare type variables remain bare
because they add no permission binder. Rendered programs can therefore enter
through surface parsing again while preserving the core AST. Core remains a subset
of surface. Diagnostic `Debug` output is separate and is not a source
serialization format.

{{property parameter_permissions_are_explicit_at_calls}}

{{property receiver_permissions_have_valid_origins}}

{{property call_generic_origins_are_hygienic}}
