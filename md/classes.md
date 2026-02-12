# Classes

Dada programs are made up of class declarations.
Each class has a name, fields, and methods.
Here is a simple class `Point` with two `Int` fields:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Point {
            x: Int;
            y: Int;
        }

        class Main {
            fn test(given self) -> Int {
                let p = new Point(22, 44);
                p.x.give;
            }
        }
    }
);
```

The `Main` class is special only by convention -- the model checks all methods in all classes.
Each method has a receiver (`self`) with a permission (here, `given`, which we'll explain later)
and a body that is type-checked against the declared return type.

New instances are created with `new Point(22, 44)`,
providing values for each field in declaration order.
Fields are accessed with dot notation (`p.x`).

## Class predicates

Classes come in three flavors, determined by a **class predicate**:

| Declaration | Predicate | Meaning |
| --- | --- | --- |
| `class Foo { }` | (default) | Unique by default, can be shared with `.share` |
| `struct Foo { }` | shared | Value type, always shared and copyable |
| `guard class Foo { }` | linear | Must be consumed, cannot be implicitly dropped |

`Int` is a built-in struct type --
since structs are always shared, `Int` values can be freely copied.
Most user-defined classes use the default `class` predicate,
which gives them unique ownership by default.

We will return to class predicates as we explore the permission system.

## Grammar

The grammar for class declarations in the model looks like this:

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
