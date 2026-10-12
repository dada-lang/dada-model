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
| `^ T`, `^[] T` | Independent unique ownership |
| `^[x, y] T` | Permission derived from the listed places |
| `shared T`, `shared[] T`, `[] T` | Independent shared ownership |
| `shared[x, y] T`, `[x, y] T` | Sharing from the listed places |
| `![x, y] T` | Mutable access from the listed places |

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
`mut` and `boxed` retain their separate meanings.

## Parameter defaults

Only the outermost permission of a receiver or input is implicit. A parameter
`x: Data` means `x: any Data`; each occurrence introduces its own fresh permission
variable. `self` likewise means `any self`. Explicit permissions such as `^Data`,
`P Data`, and `[source] Data` keep their stated meaning.

For a parameter `x: Array[Data]`, only the permission on `Array` is introduced.
The element type remains owned. Field types, return types, local annotations,
and nested type arguments retain their owned default. To require ownership of a
parameter explicitly, write `x: ^Data`; for a receiver, write `^self`.

For example, this surface declaration:

{anchor}`surface_generic_permission_example`

has the following explicit core signature (fresh names are illustrative):

{anchor}`core_generic_permission_example`

These snippets are the two sides of an `assert_desugars!` test. It lowers the
surface program and compares its AST with the independently parsed core program,
ignoring bound-variable names. This checks the expansion itself; type checking
and interpretation have separate tests.

## Calls supply all permissions

There is no generic argument inference. Generated permission parameters follow
all explicitly declared generics, in receiver-first, then input-left-to-right
order. An explicit permission contributes no extra slot. Calls must supply every
argument, including the generated suffix:

{anchor}`explicit_generated_permission_call`

The checker resolves the actual method before checking argument count and kinds.
An incorrect list reports the expanded signature and associates generic slots
with the receiver or inputs that use them. The entry method has no caller-supplied
generic arguments, so executable examples use `fn main(^self)`.
Place origins written in call arguments belong to the caller, even when the
callee uses the same names for its receiver, inputs, or locals.

## Places and values

A bare `place` or `place.share` shares from that place. `place^` gives its value;
`place!` creates a mutable lease. `place^.share` first gives, then shares the value
independently. The outer independent permission does not erase dependencies in
nested field or element types. `drop place;` is a statement; it cannot be used
where an expression is required.

Core is the explicit language used by the judgments. Its source renderer emits
explicit parameter permissions and named generic binders, so rendered programs
can enter through surface parsing again. Diagnostic `Debug` output is separate
and is not a source serialization format.

{{property parameter_permissions_are_explicit_at_calls}}

{{property receiver_permissions_have_valid_origins}}

{{property call_generic_origins_are_hygienic}}
