# Sharing places

In the [giving chapter](./giving.md), we saw how `^` transfers ownership.
Sometimes you want to read a value while leaving it in its original place.
A bare place expression, such as `foo`, shares that place. You can write the
same operation explicitly as `foo.share`.

## Sharing a place and sharing a value

Both operations create shared values, but they record different dependencies:

| Expression | Operation | Resulting permission |
| --- | --- | --- |
| `foo` or `foo.share` | Share the place `foo` | `shared[foo]` |
| `foo^.share` | Give the value from `foo`, then share that value | `shared[]` |
| `new Foo().share` | Share a newly created value | `shared[]` |

`shared[]`, also written `shared`, introduces no place dependency. Sharing a
place preserves its origin in the permission. Permissions in the underlying
type can introduce further dependencies; composing permissions does not erase
those restrictions. See [Sharing values](./sharing.md).

## A simple example

This program creates a `Foo`, shares its place, and then uses both the original
and the shared result:

{anchor}`simple_borrow`

After `foo.share`, we can still read `foo.i`. Reading shared data does not
prevent other reads. Let's walk through how the checker handles this.

### Typing `foo.share`

The checker uses the `share place` rule:

{judgment-rule}`type_expr, share place`

First, `access_permitted(env, ..., Access::SharePlace, place)` checks the liens
of live variables for conflicting accesses. Then `env.place_ty(place)` finds
the place's type. The result applies `shared[foo]` to the underlying type,
with the outer permission stripped: `shared[foo] Foo`.

The corresponding `access_ty` rule constructs the same type:

{judgment-rule}`access_ty, share`

The permission records **which place was shared**. While the resulting value
is live, the checker restricts changes to `foo` that would invalidate it.

### How access control works

When the checker reaches `foo.i.share`, the environment contains:

| Variable | Type |
| --- | --- |
| `self` | `given Main` |
| `foo` | `Foo` |
| `bar` | `shared[foo] Foo` |

Sharing `foo.i` must be compatible with every live variable's type.
The judgment `env_permits_access` performs these checks:

{judgment-rule}`env_permits_access, env_permits_access`

Here `bar` is live because `bar^` appears later, so the checker includes its
`shared[foo] Foo` type.

### Liens

A **lien** is an access constraint embedded in a type:

{anchor}`Lien`

`Lien::Share(place)` records that the place is shared.
`Lien::Mt(place)` records a mutable borrow of the place.
The `liens` judgment extracts these constraints from permissions:

{judgment-rule}`liens, perm-shared`

For `Perm::SharedFrom(places)`, it creates a `Lien::Share` for each origin,
as well as the dependencies inherited from that origin's type.
For example, `shared[foo] Foo` yields `Lien::Share(foo)`.
Independent `shared[]` introduces no origin lien.

### What sharing permits

The `shared` rule checks a sharing lien against an access:

{judgment-rule}`lien_permit_access, shared`

It delegates to:

{judgment}`shared_place_permits_access`

The three rules permit different accesses:

- **`share-share`** allows sharing any place. Reads are compatible with reads.
- **`share-mutation`** allows mutable access or dropping only when the accessed
  place is **disjoint** from the shared place.
- **`share-give`** allows giving a place that is **disjoint from or a prefix of**
  the shared place. Moving a prefix preserves dependencies at the destination.

These checks govern sharing a place. Sharing a value with `expr.share` instead
checks the inner expression, proves its type shareable, and applies `shared[]`.
For `foo^.share`, the inner `foo^` must pass the giving checks first.

In our example, `foo.i.share` is checked against `Lien::Share(foo)`.
The `share-share` rule succeeds because sharing the whole object is compatible
with sharing one of its fields.

## Mutation through shared data is an error

Sharing a place grants read access. A mutable borrow of an overlapping field
conflicts with a live shared use:

{anchor}`mutation_through_ref_is_error`

The `share-mutation` rule requires `foo.i` to be disjoint from the shared place
`foo`. It is a sub-place of `foo`, so the check fails. While the shared use is
live, the original data cannot be mutated through `foo` or its fields.

## Giving a field of shared data is an error

Similarly, you cannot give away a field of a place with a live shared use:

{anchor}`giving_field_while_refd_is_error`

`foo.i` is neither disjoint from nor a prefix of `foo`, so `share-give` fails.
Giving just that field would leave the original object partially moved while
`bar` still depends on the whole object.

The prefix exception permits moving the whole object. After
`let moved = foo^`, a live shared use of `foo` depends on `moved`, and a shared
use of `foo.i` depends on `moved.i`. The checker updates dependent types to
preserve those restrictions. The [Moves preserve dependencies
property](./giving.md#moves-preserve-dependencies) documents this behavior and
its tested scope.

## Liveness cancels restrictions

Liens matter while the variable carrying them is **live**: later code might
still use it. Once that variable has no further uses, its restrictions vanish:

{anchor}`liveness_cancels_restrictions`

Here `bar` mutably borrows `foo`, but the program then shares `foo.i`.
A live mutable borrow would block this access. However, `bar` is never used
after `let i = ...`, so its type `![foo] Foo` is absent from the checker's set
of live types. Its lien no longer blocks sharing the field.

This resembles Rust's non-lexical lifetimes: an access constraint can end at
last use rather than at the end of the enclosing scope.

## Mutable borrows are more restrictive

A mutable lien blocks all overlapping accesses, including sharing:

{judgment}`mut_place_permits_access`

- **`lease-mutation`** permits sharing, mutable access, or dropping only for
  places disjoint from the leased place.
- **`lease-give`** permits giving places disjoint from or a prefix of the leased
  place, preserving dependencies when a prefix moves.

This example fails:

{anchor}`mut_borrow_blocks_read`

`bar` is live because `bar^` occurs later. Its `Lien::Mt(foo)` is active, and
`foo.i` overlaps `foo`, so the attempt to share the field is rejected.

## Disjoint access is fine

Sharing or mutably borrowing `foo` does not prevent accessing unrelated data:

{anchor}`disjoint_access_is_fine`

`bar` shares `foo`, creating `Lien::Share(foo)`. Giving `other` is permitted
because `other` and `foo` are disjoint variables.

## Transitive restrictions

Sharing a place also preserves dependencies in that place's type:

{anchor}`transitive_restrictions`

Here `q` has type `![p] Foo` and `r` has type `shared[q] Foo`. The liens of
`r` include both `Lien::Share(q)` and the `Lien::Mt(p)` inherited from `q`.
Consequently, `p.i.share` is rejected by `lease-mutation`: `p.i` overlaps `p`.

Although `q` has no further uses after `let r`, the live variable `r` still
carries the transitive dependency on `p`.

Giving a value can preserve a mutable borrow, but only when all possible
origins supply the required capability:

{{property given_from_mut_requires_mut_origins}}

{{property sharing_does_not_grant_mut}}

{{property given_from_preserves_origin_dependencies}}

## Access constraints

| Access | Permission | Lien | Permits sharing the origin? | Permits mutating the origin? |
| --- | --- | --- | --- | --- |
| `place` or `place.share` | `shared[place]` | `Lien::Share(place)` | Yes | No |
| `place!` | `![place]` | `Lien::Mt(place)` | No | No |

The checker extracts liens from live types, compares the affected places for
overlap, and uses liveness to release restrictions after the last use.
