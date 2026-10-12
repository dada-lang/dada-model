# Shared permissions

Some permissions are **shared**.
Any shared permission can be duplicated.
This is expressed by the predicate `P is shared`, which includes sharing from
places as well as independent shared ownership.
Here are three examples of shared permissions in Dada,
and understanding how they relate to each other
is key to understanding permission comparison.

## Examples of shared permissions

**`shared`**, also written **`shared[]`**, means independent shared ownership.
Such a value can be duplicated freely
and lives as long as any copy exists.
It places no restrictions on the environment.

**`shared[d]`** means sharing from the place `d`.
It can be duplicated freely, but depends on `d`.
While the shared result is live, `d` cannot be modified.

**`shared ![d]`** -- a composed permission.
This is the result of *sharing* a lease:
you take a mutable lease `![d]`
and share the resulting value, for example with `lease^.share`.
The result is shared (because the outer `shared` makes it so),
but it still restricts `d`
(because the underlying lease is active).

{{property given_from_duplication_requires_shared_origins}}

## How they relate

These three form a subtyping chain:

```text
shared  <:  shared[d]  <:  shared ![d]
```

Each step adds more restrictions while remaining shared.

### `shared <: shared[d]`

An independently shared value can stand in wherever sharing from `d` is expected.
Giving an owned shared copy is safe --
they get what they need (read access),
and the extra restriction on `d`
(not modifying it while the shared result is live)
is harmlessly conservative:

{anchor}`copy_perm_shared_subtype_ref`

The value `s` has type `shared Data`.
The target `r` expects `shared[d] Data`.
Since `shared <: shared[d]`, this works.

### `shared[d]` is NOT `<: shared`

The reverse doesn't hold --
a place dependency cannot become independent ownership:

{anchor}`copy_perm_ref_not_subtype_shared`

`shared[d] </: shared` --
the shared value depends on `d` being available.
A `shared` value makes no such assumption.
If we allowed this,
the "shared" value could outlive `d`.

### `shared <: shared ![d]`

A shared value can also stand in for a shared lease.
The shared lease restricts `d`;
a shared value doesn't need `d` at all,
so the restriction is harmlessly extra:

{anchor}`copy_perm_shared_subtype_shared_mut`

### `shared[d] <: shared ![d]`

Sharing from a place can stand in for a shared lease
from the same place:

{anchor}`copy_perm_ref_subtype_shared_mut`

Both `shared[d]` and `shared ![d]` are shared
and both restrict `d`.
The difference is what they say about the *object* --
`shared[d]` grants read access to the object,
while `shared ![d]` allows the possibility
that another `![d]` holder could mutate the object.
Since sharing the place provides a stronger guarantee,
it's a subtype.

The chain comparison rule for this is:

{judgment-rule}`red_chain_sub_chain, (shared[place]::P) vs (shared[]::mut::P)`

### `shared ![d]` is NOT `<: shared[d]`

The reverse fails:

{anchor}`copy_perm_shared_mut_not_subtype_ref`

`shared ![d] </: shared[d]` --
a shared lease can coexist with mutation of the object,
while direct sharing from the place cannot.
Treating a shared lease as direct sharing
would falsely promise immutability.

## How composition works

Permissions compose with `Perm::Apply` --
written as `P Q` in the grammar,
meaning "apply permission `P` to something with permission `Q`."
The result depends on whether the inner permission is shared.

### Shared permissions absorb: `shared[p] shared == shared`

When you share a place containing independently shared data,
the place dependency is redundant:

{anchor}`copy_perm_ref_shared_absorbs`

The expression `d.share` has type `shared[d] shared Data`.
But `d` has type `shared Data`,
so the composed permission `shared[d] shared`
reduces to just `shared` --
the result remains independently shared.

Internally, this is the `append_chain` rule:
when the right-hand side of a composition is shared,
the left-hand side is discarded.
The inner shared permission determines the resulting access.

### Non-shared composes: `shared[p] ![d]`

When the inner permission is not shared,
composition creates a genuine chain.
Sharing a place containing a lease
retains the lease dependency:

{anchor}`copy_perm_ref_mut_composes`

Here `p.share` creates `shared[p] ![d] Data` --
a chain of two links.
The permission records that you shared the place `p`,
which itself was leased from `d`.

What happens when you want to *use* this value
depends on whether `p` is still alive --
the [Liveness and cancellation](./liveness.md) chapter
explains how dead links are resolved during comparison.

## `![d]` is not shared

A mutable lease `![d]` is not shared --
it provides exclusive mutable access,
which can't be duplicated:

{anchor}`copy_perm_mut_not_subtype_ref`

`![d] </: shared[d]` --
a lease grants exclusive mutation rights,
while sharing the place only grants read access.
These are incomparable: neither is a subtype of the other.

Similarly, `given` (unique ownership) is not comparable
to any of the shared permissions:

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
| `shared` | `shared[d]` | Yes | Independent ownership satisfies a place dependency |
| `shared[d]` | `shared` | No | A place dependency cannot become ownership |
| `shared[d1]` | `shared[d1, d2]` | Yes | Fewer sources = more specific |
| `shared[d1, d2]` | `shared[d1]` | No | Can't drop a possible origin |
| `shared[d]` | `shared ![d]` | Yes | Sharing the place is stronger than sharing a lease |
| `shared ![d]` | `shared[d]` | No | Shared lease doesn't guarantee immutability |

The shared permissions (`shared`, `shared[d]`, `shared ![d]`)
form a chain within this landscape.
The non-shared permissions (`given`, `![d]`) are incomparable
with the shared permissions.

## Summary

The shared permissions form a hierarchy:

| Permission | Copy? | Owned? | Restricts environment? |
| --- | --- | --- | --- |
| `shared` | yes | yes | no |
| `shared[d]` | yes | no | `d` cannot be modified |
| `shared ![d]` | yes | no | `d` cannot be modified |

Subtyping: `shared <: shared[d] <: shared ![d]`.

Composition: applying a permission to something shared
just gives you the shared permission back.
Applying a permission to something non-shared
creates a genuine chain that requires
further analysis to resolve.

The non-shared permissions (`given`, `![d]`)
sit outside this hierarchy --
they are incomparable with the shared permissions.
