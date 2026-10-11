# Classes and structs

Dada programs declare classes and structs. Each declaration has a name, fields,
and methods. Here is a simple struct `Point` with two `Int` fields:

{anchor}`classes_point_example`

The entry type `Main` is special only by convention -- the model checks every method.
Each method has a receiver (`self`) with a permission (here, `^`, which we'll explain later)
and a body that is type-checked against the declared return type.

New instances are created with `new Point(22, 44)`,
providing values for each field in declaration order.
Fields are accessed with dot notation (`p.x`).

## Declaration categories

Three declaration forms select a **class predicate** in the model:

| Declaration | Predicate | Meaning |
| --- | --- | --- |
| `class Foo { }` | `Class` | Affine data; may have a destructor; cannot be shared as a value |
| `struct Foo { }` | `Struct` | Shareable data with mutable fields; no destructor |
| `shared struct Foo { }` | `Shared` | Copyable when its generic arguments are shared; no destructor |

`Int` is a built-in shared struct type, so its values can be freely copied.
A plain `class` keeps ownership uniquely tracked and allows a destructor.
Declaring a `struct` opts into sharing and rules out a destructor; declaring a
`shared struct` also makes values copyable without an explicit sharing operation
when all of its generic arguments are shared (automatically true with no arguments).
The checker rejects nonempty drop bodies on either struct form.

We will return to class predicates as we explore the permission system.

## Grammar

The core grammar uses `ClassDecl` for all three declaration categories:

{anchor}`ClassDecl`

The `#[term(...)]` attributes define the parsing grammar using formality-core conventions:
`$?` is an optional element, `$*` means zero-or-more, `$,` means comma-separated,
and `$:where` means the keyword `where` appears only if the list is non-empty.
`Binder` introduces generic parameters that are in scope for the bound data.

Each field has a name and a type,
and can optionally be declared `atomic`
(which affects variance -- more on this later):

{anchor}`FieldDecl`

{anchor}`Atomic`

{{property only_classes_have_destructors}}
