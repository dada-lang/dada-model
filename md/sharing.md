# Sharing values

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

Sharing a value expression, such as `new Data().share` or `d^.share`, converts
unique (`^`) ownership to independent shared ownership, `shared[]`.
The shorter permission spelling `shared` means the same thing.
Once shared, a value can be freely copied:

{anchor}`sharing_a_value`

Compare this with the [giving a value twice](./giving.md#giving-a-value-twice-is-an-error)
example from the previous chapter, which failed.
The difference is `.share` --
it transforms the `Data` value so that subsequent gives copy rather than move.

Sharing a place directly is a different operation. `d` and `d.share` both yield
`shared[d] Data`, keeping a dependency on `d`. To share its value independently,
write `d^.share`: first give the value, then share it. The [Sharing places
chapter](./borrowing.md) explains place dependencies.

## The `share value` rule

The type checker handles sharing a value with this rule:

{judgment-rule}`type_expr, share value`

The rule has two premises:

- **`type_expr(env, ..., &*expr) => (env, ty)`** --
  Type-check the inner expression, producing a type `ty`.

- **`prove_is_shareable(&env, &ty) => ()`** --
  Verify that the type is allowed to be shared.
  Not all types can be shared -- given classes cannot.

If both premises succeed,
the result type is `shared ty` --
the original type wrapped with the `shared[]` permission. Dependencies already
present in the inner type still matter; for example, sharing a mutable lease
does not remove the lease's origin.

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
The "copy" rule requires `prove_is_shared`:

{judgment-rule}`move_place, copy`

A `shared Data` type satisfies `prove_is_shared`
because any shared permission can be duplicated.
So when you write `s^` on a shared value,
the "copy" rule fires and the value is copied rather than moved.

This is why the example above works --
both `s^` expressions copy the shared value.

## Shared classes are always shared

In the previous chapter, we saw that `Int` values
can be [given multiple times](./giving.md#shared-classes-are-copyable).
That's because `Int` is a shared class type --
it has the `Shared` class predicate,
which means it is *always* shared and copyable
without needing an explicit `.share`:

{anchor}`shared_classes_always_shared`

Shared classes are always copyable,
but their fields cannot be individually mutated.
Regular classes are mutable by default but require `.share`
to become copyable.

## Given classes cannot be shared

Given classes cannot be shared.
Attempting to share a given class is an error:

{anchor}`given_classes_cannot_be_shared`

The `prove_is_shareable` premise fails
because `Resource` has the `Given` predicate,
which does not satisfy `share(Resource)`.

## Sharing is idempotent

Sharing an already-shared value is fine --
it's a no-op:

{anchor}`sharing_is_idempotent`

The inner `.share` produces `shared Data`.
The outer `.share` checks `prove_is_shareable` on `shared Data`,
which succeeds because a shared permission is always shareable.
The result is still `shared Data` --
applying `shared` to an already-shared type normalizes
to the same type.

## Shareable, shared, and owned

These predicates describe different properties:

- `T is share` means values of `T` can be shared as values.
- `T is shared` means values of `T` are shared and can be duplicated. This includes
  values obtained by sharing a place; it does not require ownership.
- `T is owned` means fully owned, with no origin dependencies.

For fully owned shared values, write both constraints:
`where T is shared, T is owned`.

The permission `shared[]` describes independent sharing; `shared[d]` describes
sharing from the place `d`. Any shared permission can be duplicated. Thus
`shared Data` is both shared and owned, while `shared[d] Data` is shared without
being owned.
An ordinary owned `Data` can be shareable without already being shared.
These predicate names do not change the class or permission syntax.

{{property given_from_owned_requires_owned_origins}}

## Independent sharing

`shared` and `shared[]` are equivalent. Neither introduces a place dependency.

{{property independent_sharing_is_owned_and_duplicable}}
