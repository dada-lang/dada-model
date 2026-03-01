# Subtyping

In the previous chapters,
we saw how types carry permissions
and how borrowing creates new permission types like `ref[place]`.
But we glossed over an important question:
what happens when a value's type doesn't *exactly* match
what's expected?

That's where **subtyping** comes in.
Subtyping lets one type stand in for another
when the substitution is safe.

## A motivating example

Here's a function that creates a shared value
but declares its return type as a reference:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self) -> ref[self] Data {
                let d: shared Data = new Data().share;
                d.give;
            }
        }
    }
);
```

The body produces `shared Data`,
but the return type is `ref[self] Data`.
These aren't the same type --
so why does this work?

The answer is subtyping:
`shared Data` is a **subtype** of `ref[self] Data`.
A shared value is "at least as good as" a reference --
if the caller expects a borrowed reference,
giving them an owned shared value is safe.
The type checker proves `shared Data <: ref[self] Data`
and accepts the program.

## When subtyping happens

Subtyping is invoked through the `type_expr_as` judgment,
which checks that an expression's type is a subtype
of some expected type:

{judgment-rule}`type_expr_as, type_expr_as`

The judgment first computes the expression's type with `type_expr`,
then calls `sub` to verify it's a subtype of the expected type.

This happens in three situations:

- **Return types** -- the body of a method is checked against
  the declared return type.
- **Let bindings with type annotations** -- `let x: T = expr`
  checks that the expression's type is a subtype of `T`.
- **Method arguments and field initialization** --
  each argument's type must be a subtype of the declared parameter type.

## Type subtyping: same class required

Dada has no class hierarchy --
there's no equivalent of Java's `extends` or Rust's trait objects.
Subtyping only works between types with the **same class name**.
The difference is in the permissions.

Here's a program where subtyping allows
a narrower reference to satisfy a wider one:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1, d2] Data {
                d1.ref;
            }
        }
    }
);
```

The expression `d1.ref` has type `ref[d1] Data`,
but the return type is `ref[d1, d2] Data`.
Both are `Data` -- same class name --
so the type checker compares the permissions:
`ref[d1] <: ref[d1, d2]`.
A reference that borrows from fewer places is more specific,
so it can safely substitute for a reference
that borrows from more places.

The `sub` judgment handles this through the "sub-classes" rule:

{judgment-rule}`sub, sub-classes`

The rule requires matching class names
and then delegates to `sub_perms`
for the permission comparison.

### Different classes are incompatible

If the class names don't match, subtyping fails:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Foo { }
        class Bar { }

        class Main {
            fn test(given self) {
                let f = new Foo();
                let b: Bar = f.give;
                ();
            }
        }
    },
    r#"judgment `type_expr_as"#,
);
```

There is no rule that can prove `Foo <: Bar` --
the "sub-classes" rule requires `name_a == name_b`,
and `Foo` and `Bar` are different names.

## Permission subtyping

Permissions form a partial order.
Not every pair is comparable,
and the relationships reflect
the safety guarantees each permission provides.

Here are the key relationships:

| Sub | Super | Holds? | Why |
| --- | --- | --- | --- |
| `given` | `given` | Yes | Same permission |
| `shared` | `shared` | Yes | Same permission |
| `given` | `shared` | No | Can't pretend unique is shared |
| `shared` | `given` | No | Can't pretend shared is unique |
| `shared` | `ref[d]` | Yes | Shared ownership is stronger than borrowing |
| `ref[d]` | `shared` | No | A borrow can't become ownership |
| `ref[d1]` | `ref[d1, d2]` | Yes | Fewer sources = more specific |
| `ref[d1, d2]` | `ref[d1]` | No | Can't drop a borrow source |

### Narrowing a reference fails

Here's the reverse of our earlier example --
trying to widen a multi-source reference into a single-source one:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                let r: ref[d1, d2] Data = d1.ref;
                r.give;
            }
        }
    },
    r#"judgment `type_expr_as"#,
);
```

`ref[d1, d2] Data` means "a reference that might borrow from `d1` or `d2`."
The return type `ref[d1] Data` promises it only borrows from `d1`.
That's a stronger guarantee than the value actually provides,
so the check fails.

### How permission comparison works

The `sub` judgment delegates permission comparison to `sub_perms`,
which **reduces** each permission into a canonical form
called a `RedPerm` -- a set of `RedChain`s.
Each chain is a sequence of links like `Shared`, `Rfl(place)`, `Mtl(place)`, etc.

The reduction resolves liveness (is a borrowed place still alive?),
expands permission composition,
and normalizes the result.
Then each chain from the subtype
must be matched by some chain in the supertype.

The [Comparing Permissions](./comparing-permissions.md) chapter
walks through the full set of rules
that govern how permissions relate to each other.

## Permission erasure on shared classes

The most elegant subtyping rule handles **shared classes** --
types like `Int`, `shared class Point`, and other value types.
For these types, permissions don't matter:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Main {
            fn test(given self) -> Int {
                let x: ref[self] Int = 0;
                x.give;
            }
        }
    }
);
```

`ref[self] Int <: Int` -- a borrow of an `Int` is just an `Int`.

This works in both directions:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Main {
            fn test(given self) -> Int {
                let x: Int = 0;
                let y: ref[self] Int = x.give;
                y.give;
            }
        }
    }
);
```

`Int <: ref[self] Int` also holds.

### The "sub-shared-classes" rule

The rule that makes this work is:

{judgment-rule}`sub, sub-shared-classes`

For shared classes, the rule **distributes** the outer permission
into the type parameters.
To check `A SharedClass[B] <: X SharedClass[Y]`,
it checks `A B <: X Y` for each parameter pair.

The key insight: when a shared class has **zero** type parameters
(like `Int`), there's nothing to distribute into.
The `for_all` over parameters is vacuously true --
so the subtyping holds regardless of what permissions `A` and `X` are.
Permissions on `Int` simply don't matter.

### Shared classes with copy parameters

The same rule extends to shared classes with parameters,
as long as those parameters are copy types:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        shared class Point {
            x: Int;
            y: Int;
        }

        class Main {
            fn test(given self) -> Point {
                let p: shared Point = new Point(1, 2);
                p.give;
            }
        }
    }
);
```

`shared Point <: Point` works because
the rule distributes: it checks `shared Int <: given Int`
for each parameter.
Since `Int` is itself a shared class with no parameters,
that check is vacuously true.

### Non-copy parameters block erasure

But if a shared class wraps a non-copy type,
the permission matters:

```rust
# extern crate dada_model;
dada_model::assert_err!(
    {
        shared class Box[ty T] {
            value: T;
        }

        class Data { }

        class Main {
            fn test(given self, d: given Data) -> Box[Data] {
                let b: ref[d] Box[Data] = new Box[Data](new Data());
                b.give;
            }
        }
    },
    expect_test::expect![[r#"
        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]
);
```

`ref[d] Box[Data] </: Box[Data]` fails because
the rule distributes: it needs `ref[d] Data <: Data`.
But `Data` is a regular class (not a shared class),
so `ref[d]` cannot be erased.
A borrowed `Data` is genuinely different from an owned `Data`.

## Place refinement

References carry the places they borrow from,
and sub-places are more specific than parent places.
A borrow from `d.left` is a subtype of a borrow from `d`:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data {
            left: given Data;
            right: given Data;
        }

        class Main {
            fn test(given self, d: given Data) -> ref[d] Data {
                d.left.ref;
            }
        }
    }
);
```

`ref[d.left] Data <: ref[d] Data` holds
because `d` is a prefix of `d.left` --
a reference that borrows from `d.left` certainly borrows from `d`.

The chain comparison rule that handles this is:

{judgment-rule}`red_chain_sub_chain, (ref::P) vs (ref::P)`

It requires `place_b.is_prefix_of(&place_a)` --
the supertype's place must be a prefix of the subtype's place.

### The reverse fails

Going the other direction doesn't work:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data {
            left: given Data;
            right: given Data;
        }

        class Main {
            fn test(given self, d: given Data) -> ref[d.left] Data {
                d.ref;
            }
        }
    },
    r#"judgment `type_expr_as"#,
);
```

`ref[d] Data </: ref[d.left] Data` --
a reference that borrows from all of `d` can't promise
it only borrows from `d.left`.
The prefix check fails: `d.left` is not a prefix of `d`.

## Summary

Subtyping in Dada operates on permissions, not class hierarchies.
Two types are related by subtyping only when they name the same class
and the subtype's permission is "at least as strong" as the supertype's.

The most important rules:

- **Shared classes absorb permissions** -- `ref[p] Int` is just `Int`,
  because shared classes with no type parameters make the
  permission comparison vacuous.
- **Narrower borrows are subtypes** -- `ref[d1] <: ref[d1, d2]`
  because borrowing from fewer places is more specific.
- **Sub-place borrows are subtypes** -- `ref[d.f] <: ref[d]`
  because a borrow from a sub-place certainly borrows from the parent.
- **Shared is stronger than borrowed** -- `shared <: ref[d]`
  because owning a shared copy is at least as good as borrowing.
