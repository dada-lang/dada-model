# Sharing

In the [previous chapter](./giving.md),
we saw that giving a non-copyable value moves it --
after a give, the original is gone.
We also saw that shared class types like `Int` are copyable
and can be given multiple times.
But what about regular classes?
What if you want to use a value in multiple places
without giving up ownership?

That's what **sharing** is for.

## Sharing a value

The `.share` operator converts a value
from unique (`given`) ownership to `shared` ownership.
Once shared, a value can be freely copied:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self) -> Data {
                let d = new Data();
                let s = d.give.share;
                s.give;
                s.give;
            }
        }
    }
);
```

Compare this with the [giving a value twice](./giving.md#giving-a-value-twice-is-an-error)
example from the previous chapter, which failed.
The difference is `.share` --
it transforms the `Data` value so that subsequent gives copy rather than move.

## The `share expr` rule

The type checker handles `.share` with this rule:

{judgment-rule}`type_expr, share expr`

The rule has two premises:

- **`type_expr(env, ..., &*expr) => (env, ty)`** --
  Type-check the inner expression, producing a type `ty`.

- **`prove_is_shareable(&env, &ty) => ()`** --
  Verify that the type is allowed to be shared.
  Not all types can be shared -- given classes cannot.

If both premises succeed,
the result type is `shared ty` --
the original type wrapped with the `shared` permission.

## Shareability and class predicates

Whether a type can be shared depends on its **class predicate**.
Classes come in three flavors:

{anchor}`ClassPredicate`

| Declaration | Predicate | Shareable? |
| --- | --- | --- |
| `given class Foo { }` | `Given` | No |
| `class Foo { }` | `Share` (default) | Yes |
| `shared class Foo { }` | `Shared` | Already shared |

The `prove_is_shareable` judgment delegates
to the general predicate-proving machinery:

{judgment-rule}`prove_is_shareable, is`

For a regular class like `Data`,
the `Share` predicate is satisfied by default,
so `.share` succeeds.

## Shared values are copyable

Once a value is shared,
the `move_place` judgment from the [giving chapter](./giving.md#the-move_place-judgment)
treats it differently.
Recall that `move_place` has two rules -- "give" (move) and "copy".
The "copy" rule requires `prove_is_copy`:

{judgment-rule}`move_place, copy`

A `shared Data` type satisfies `prove_is_copy`
because the `shared` permission is a copy permission.
So when you write `s.give` on a shared value,
the "copy" rule fires and the value is copied rather than moved.

This is why the example above works --
both `s.give` expressions copy the shared value.

## Shared classes are always shared

In the previous chapter, we saw that `Int` values
can be [given multiple times](./giving.md#shared-classes-are-copyable).
That's because `Int` is a shared class type --
it has the `Shared` class predicate,
which means it is *always* shared and copyable
without needing an explicit `.share`:

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
                let p = new Point(22, 44);
                p.give;
                p.give;
            }
        }
    }
);
```

Shared classes are always copyable,
but their fields cannot be individually mutated.
Regular classes are mutable by default but require `.share`
to become copyable.

## Given classes cannot be shared

Given classes cannot be shared.
Attempting to share a given class is an error:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        given class Resource { }

        class Main {
            fn test(given self) -> shared Resource {
                let r = new Resource();
                r.give.share;
            }
        }
    },
    r#"the rule "share expr" at (*) failed"#,
);
```

The `prove_is_shareable` premise fails
because `Resource` has the `Given` predicate,
which does not satisfy `share(Resource)`.

## Sharing is idempotent

Sharing an already-shared value is fine --
it's a no-op:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self) -> Data {
                let d = new Data();
                d.give.share.share;
            }
        }
    }
);
```

The inner `.share` produces `shared Data`.
The outer `.share` checks `prove_is_shareable` on `shared Data`,
which succeeds because a shared permission is always shareable.
The result is still `shared Data` --
applying `shared` to an already-shared type normalizes
to the same type.
