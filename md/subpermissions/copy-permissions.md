# Copy permissions

Some permissions are **copy** --
values with copy permissions can be freely duplicated.
There are three copy permissions in Dada,
and understanding how they relate to each other
is key to understanding permission comparison.

## The three copy permissions

**`shared`** -- owned and copy.
A shared value can be duplicated freely
and lives as long as any copy exists.
It places no restrictions on the environment.

**`ref[d]`** -- borrowed and copy.
A reference can be duplicated freely,
but it borrows from the place `d`.
While the reference exists,
`d` cannot be modified.

**`shared mut[d]`** -- a composed permission.
This is the result of *sharing* a lease:
you take a mutable lease `mut[d]`
and share it with `.share`.
The result is copy (because the outer `shared` makes it so),
but it still restricts `d`
(because the underlying lease is active).

## How they relate

These three form a subtyping chain:

```text
shared  <:  ref[d]  <:  shared mut[d]
```

Each step adds more restrictions while remaining copy.

### `shared <: ref[d]`

A shared value can stand in wherever a reference is expected.
If the caller expects a borrowed reference from `d`,
giving them an owned shared copy is safe --
they get what they need (read access),
and the extra restriction on `d`
(not modifying it while the reference exists)
is harmlessly conservative:

{anchor}`copy_perm_shared_subtype_ref`

The value `s` has type `shared Data`.
The target `r` expects `ref[d] Data`.
Since `shared <: ref[d]`, this works.

### `ref[d]` is NOT `<: shared`

The reverse doesn't hold --
a borrow can't become ownership:

{anchor}`copy_perm_ref_not_subtype_shared`

`ref[d] </: shared` --
the reference depends on `d` being alive.
A `shared` value makes no such assumption.
If we allowed this,
the "shared" value could outlive `d`.

### `shared <: shared mut[d]`

A shared value can also stand in for a shared lease.
The shared lease restricts `d`;
a shared value doesn't need `d` at all,
so the restriction is harmlessly extra:

{anchor}`copy_perm_shared_subtype_shared_mut`

### `ref[d] <: shared mut[d]`

A reference can stand in for a shared lease
from the same place:

{anchor}`copy_perm_ref_subtype_shared_mut`

Both `ref[d]` and `shared mut[d]` are copy
and both restrict `d`.
The difference is what they say about the *object* --
`ref[d]` guarantees the object won't be mutated through this reference,
while `shared mut[d]` allows the possibility
that another `mut[d]` holder could mutate the object.
Since the reference provides a stronger guarantee,
it's a subtype.

The chain comparison rule for this is:

{judgment-rule}`red_chain_sub_chain, (ref::P) vs (shared::mut::P)`

### `shared mut[d]` is NOT `<: ref[d]`

The reverse fails:

{anchor}`copy_perm_shared_mut_not_subtype_ref`

`shared mut[d] </: ref[d]` --
a shared lease can coexist with mutation of the object,
while a reference cannot.
Treating a shared lease as a reference
would falsely promise immutability.

## How composition works

Permissions compose with `Perm::Apply` --
written as `P Q` in the grammar,
meaning "apply permission `P` to something with permission `Q`."
The result depends on whether the inner permission is copy.

### Copy absorbs: `ref[p] shared == shared`

When you borrow from something that's already shared,
the borrow is redundant -- you just get shared:

{anchor}`copy_perm_ref_shared_absorbs`

The expression `d.ref` has type `ref[d] shared Data`.
But `d` has type `shared Data`,
so the composed permission `ref[d] shared`
reduces to just `shared` --
borrowing from shared gives you shared.

Internally, this is the `append_chain` rule:
when the right-hand side of a composition is copy,
the left-hand side is discarded.
The permission of the thing you're borrowing from
is what matters, not the act of borrowing.

### Non-copy composes: `ref[p] mut[d]`

When the inner permission is NOT copy,
composition creates a genuine chain.
Borrowing from something leased
gives you a borrow-of-a-lease:

{anchor}`copy_perm_ref_mut_composes`

Here `p.ref` creates `ref[p] mut[d] Data` --
a chain of two links.
The permission records that you borrowed from `p`,
which itself was leased from `d`.

What happens when you want to *use* this value
depends on whether `p` is still alive --
the [Liveness and cancellation](./liveness.md) chapter
explains how dead links are resolved during comparison.

## `mut[d]` is not copy

It's worth noting what's NOT in the copy family.
A mutable lease `mut[d]` is NOT copy --
it provides exclusive mutable access,
which can't be duplicated:

{anchor}`copy_perm_mut_not_subtype_ref`

`mut[d] </: ref[d]` --
a lease grants exclusive mutation rights,
while a reference only grants shared read access.
These are incomparable: neither is a subtype of the other.

Similarly, `given` (unique ownership) is not comparable
to any of the copy permissions:

{anchor}`copy_perm_given_not_subtype_shared`

`given </: shared` --
unique ownership and shared ownership
represent fundamentally different memory models.

## The full permission landscape

Here's how all the permissions relate:

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
| `ref[d]` | `shared mut[d]` | Yes | Reference is stronger than shared lease |
| `shared mut[d]` | `ref[d]` | No | Shared lease doesn't guarantee immutability |

The copy permissions (`shared`, `ref[d]`, `shared mut[d]`)
form a chain within this landscape.
The non-copy permissions (`given`, `mut[d]`) are incomparable
with the copy permissions.

## Summary

The copy permissions form a hierarchy:

| Permission | Copy? | Owned? | Restricts environment? |
| --- | --- | --- | --- |
| `shared` | yes | yes | no |
| `ref[d]` | yes | no | `d` cannot be modified |
| `shared mut[d]` | yes | no | `d` cannot be modified |

Subtyping: `shared <: ref[d] <: shared mut[d]`.

Composition: applying a permission to something copy
just gives you the copy permission back.
Applying a permission to something non-copy
creates a genuine chain that requires
further analysis to resolve.

The non-copy permissions (`given`, `mut[d]`)
sit outside this hierarchy --
they are incomparable with the copy permissions.
