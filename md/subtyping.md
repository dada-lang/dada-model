# Subtyping

In the previous chapters,
we saw how types carry permissions
and how sharing a place creates a permission such as `shared[place]`.
But we glossed over an important question:
what happens when a value's type doesn't *exactly* match
what's expected?

That's where **subtyping** comes in.
Subtyping lets one type stand in for another
when the substitution is safe.

## A motivating example

Here's a simple function that creates a `Data` value
and returns it:

{anchor}`subtyping_given_invisible`

The annotation `let d: given Data` makes the permission explicit,
but the return type is just `Data` -- no permission written.
These match because `given` is the **default permission** for return types,
fields, local annotations, and nested type arguments.
In those positions, `Data` means `given Data`. An outermost surface input type
that names a class or struct instead introduces a fresh permission variable.
A bare type variable `T` retains the identity permission `given`, preserving
the type supplied for `T` without a separate permission parameter. See
[Surface syntax](./surface-syntax.md#parameter-defaults).
So both sides are `given Data`, and subtyping is trivially satisfied.

But what about less trivial cases?
Consider a function that shares a place and returns the result:

{anchor}`subtyping_ref_composition_given`

The expression `d.share` creates a shared value
with type `shared[d] Data`.
The return type is also `shared[d] Data` -- an exact match.
But internally, the type checker needs to verify
that the permission `shared[d]` on the expression's type
is compatible with the permission `shared[d]` on the return type.
That verification happens through **permission reduction** --
a process we'll explain in this chapter.

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

## Type subtyping: same declaration required

Dada has no inheritance hierarchy --
there's no equivalent of Java's `extends` or Rust's trait objects.
Subtyping only works between types with the **same declared type name**.
The difference is always in the permissions.

The `sub` judgment handles this through the "sub-classes" rule:

{judgment-rule}`sub, sub-classes`

The rule requires matching declared type names
and then delegates to `sub_perms`
for the permission comparison.

### Different declarations are incompatible

If the declared type names don't match, subtyping fails:

{anchor}`subtyping_different_classes_fail`

There is no rule that can prove `Foo <: Bar` --
the "sub-classes" rule requires `name_a == name_b`,
and `Foo` and `Bar` are different names.

## Reduced permissions

The `sub_perms` judgment doesn't compare permissions directly.
Instead, it first **reduces** each permission
into a canonical form called a `RedPerm`,
then compares the reduced forms.

Why not compare permissions directly?
Because permissions as written in source code
have structure -- composition, place sets, liveness dependencies --
that makes direct comparison impractical.
Reduction normalizes all of this into a uniform representation.

### What is a RedPerm?

A `RedPerm` is a **set of `RedChain`s**.
Each `RedChain` is a **sequence of `RedLink`s**.
Links are the atomic building blocks of reduced permissions:

| RedLink | Source permission | Meaning |
| --- | --- | --- |
| *(empty chain)* | `given` | Unique ownership |
| `Shared` | `shared` | Shared ownership (copy) |
| `ShareLive(place)` | `shared[place]` | Sharing origin is **live** |
| `ShareDead(place)` | `shared[place]` | Sharing origin is **dead** |
| `Mtl(place)` | `![place]` | Mutable lease, place is **live** |
| `Mtd(place)` | `![place]` | Mutable lease, place is **dead** |

Notice the live/dead distinction:
`shared[d]` reduces to `ShareLive(d)` if `d` is still used later in the program,
and `ShareDead(d)` if it isn't.
The same for `![d]` → `Mtl(d)` or `Mtd(d)`.
This distinction matters for permission comparison --
dead permissions can be cancelled or promoted,
as we'll see in the
[Liveness and cancellation](./subpermissions/liveness.md) chapter.

### Reducing simple permissions

The simplest reductions are direct translations:

- **`given`** → one chain: `[]` (the empty chain).
  No links -- just ownership. This is the identity permission.

- **`shared`** → one chain: `[Shared]`.
  A single link indicating shared ownership.

- **`shared[d]`** (where `d` is live) → one chain: `[ShareLive(d)]`.
  A single place-sharing link.

- **`![d]`** (where `d` is live) → one chain: `[Mtl(d)]`.
  A single mutable lease link.

### Multi-place permissions become multiple chains

When a permission mentions multiple places,
it produces **one chain per place**.
This is why `RedPerm` is a *set* of chains:

- **`shared[d1, d2]`** → two chains: `{ [ShareLive(d1)], [ShareLive(d2)] }`.

The set representation means that
`shared[d1, d2]` describes a permission
that may share from `d1` *or* `d2` (or both).
For the subtype to hold,
every chain in the subtype's `RedPerm`
must be matched by some chain in the supertype's `RedPerm`.

## Composition: how permissions combine

Permissions combine when you access a field
through a shared value or a mutable lease.
If `r` has type `shared[d] Outer`
and `Outer` has a field `i: Inner`,
then the place `r.i` has type `shared[d] Inner` --
the `shared[d]` permission wraps the field's type.
Using bare `r.i` as an expression additionally shares that place, producing
`shared[r.i] Inner`; expanding that origin retains the dependency on `d`.

Internally, this creates a **composed permission**:
`Perm::Apply(shared[d], given)` -- the outer `shared[d]` applied
to the field's `given` permission.
How does reduction handle this?

### The `append_chain` rule

When reducing a composed permission `P Q`,
the type checker reduces `P` and `Q` separately,
then **appends** the chains using `append_chain`.

The rule has two cases:

- **If the right-hand chain is shared** (`Shared`, `ShareLive`, etc.):
  the left-hand side is **discarded**.
  Copy permissions absorb anything applied to them.

- **If the right-hand chain is NOT copy** (`given`, `Mtl`, etc.):
  the chains are **concatenated** into a longer chain.

### Example: `shared[d]` applied to `given`

Consider accessing a field through a shared value:

{anchor}`subtyping_field_through_ref`

The place `r.i` has type `shared[d] Inner` --
but internally, the field `i` has type `Inner` (which is `given Inner`),
and accessing it through `r: shared[d] Outer` composes them.

Reduction of the composed permission:
- `shared[d]` → `[ShareLive(d)]`
- `given` → `[]` (empty chain, not copy)
- Append: `[ShareLive(d)]` ++ `[]` = `[ShareLive(d)]`

The `given` disappears.
Since the empty chain represents identity,
appending it to anything is a no-op.
This is why `shared[d] given Inner` and `shared[d] Inner` are equivalent --
`given` is the identity permission.

### Example: `shared[w]` applied to `shared` (copy absorbs)

Now consider a field whose type is a shared struct:

{anchor}`subtyping_ref_shared_absorbs`

The field `p` has type `Point`, which is a `shared struct`.
Accessing `r.p` through `r: shared[w] Wrapper`
composes `shared[w]` with `shared` (the permission of `Point`).

Reduction:
- `shared[w]` → `[ShareLive(w)]`
- `shared` → `[Shared]` (copy!)
- Append: `[ShareLive(w)]` ++ `[Shared]` → `[Shared]`

The `shared[w]` is **discarded**.
Because `shared` is a copy permission,
the `append_chain` rule drops the left-hand side entirely.
The result is just `[Shared]` -- plain shared ownership.

This makes intuitive sense:
if the field is already shared (freely copyable),
sharing its container adds no restriction.
You just get a shared copy.

That's why `r.p->` has type `Point` (i.e., `shared Point`)
even though we accessed it through a shared place --
the `shared[w]` was absorbed by the `shared`.

### Example: `shared[p]` applied to `![d]`

Now consider sharing a place containing a mutable lease:

{anchor}`subtyping_ref_through_mut`

The expression `p.share` has type `shared[p] Data`,
and `p` has type `![d] Data`.
If we were to access a field of this value,
the composed permission would be `Apply(shared[p], ![d])`.

Reduction:
- `shared[p]` → `[ShareLive(p)]`
- `![d]` → `[Mtl(d)]` (not copy!)
- Append: `[ShareLive(p)]` ++ `[Mtl(d)]` = `[ShareLive(p), Mtl(d)]`

This is a genuine two-link chain.
The `![d]` is not copy, so it doesn't absorb --
the chain records both links.
This chain means "sharing from `p`,
which is itself a mutable lease from `d`."

Whether this chain can match some target permission
depends on liveness and cancellation rules --
if `p` is dead, reduction produces `ShareDead(p)`, which may be resolved.
That's covered in the
[Liveness and cancellation](./subpermissions/liveness.md) chapter.

## How comparison works

The `sub_perms` judgment ties it all together:

{judgment-rule}`sub_perms, sub_red_perms`

1. **Reduce** both permissions to `RedPerm`s
2. **For every chain** in the subtype's `RedPerm`,
   find a matching chain in the supertype's `RedPerm`

"Matching" means `red_chain_sub_chain` --
a judgment with rules for each kind of link comparison.
The [Subtypes and subpermissions](./subpermissions.md) chapter
walks through these rules in detail:

- [**Place ordering**](./subpermissions/place-ordering.md) --
  `shared[d.f] <: shared[d]` because sub-places are more specific.
- [**Copy permissions**](./subpermissions/copy-permissions.md) --
  `shared <: shared[d]` because independent ownership satisfies a place dependency.
- [**Liveness and cancellation**](./subpermissions/liveness.md) --
  dead links can be dropped or promoted during comparison.

## Shared structs and permission distribution

Shared structs get a special subtyping rule.
Because a shared struct's direct fields
must already be shared (copy) types,
the outer permission only matters
insofar as it affects the **type parameters**.

Consider `Int` -- a shared struct with no type parameters:

{anchor}`subtyping_perm_erasure_ref_int`

`shared[self] Int <: Int` -- sharing an `Int` still yields an `Int`.

This works in both directions:

{anchor}`subtyping_perm_erasure_int_to_ref`

`Int <: shared[self] Int` also holds.

### The "sub-shared-classes" rule

The rule that makes this work is:

{judgment-rule}`sub, sub-shared-classes`

For shared structs, the rule **distributes** the outer permission
into the type parameters.
To check `A SharedStruct[B] <: X SharedStruct[Y]`,
it checks `A B <: X Y` for each parameter pair.

The key insight: when a shared struct has **zero** type parameters
(like `Int`), there's nothing to distribute into.
The `for_all` over parameters is vacuously true --
so the subtyping holds regardless of what permissions `A` and `X` are.
The outer permission is irrelevant because there are no type parameters
for it to affect.

### Shared structs with copy parameters

The same rule extends to shared structs with parameters,
as long as those parameters are copy types:

{anchor}`subtyping_shared_class_copy_params`

`shared Point <: Point` works because
the rule distributes: it checks `shared Int <: given Int`
for each parameter.
Since `Int` is itself a shared struct with no parameters,
that check is vacuously true.

### Non-copy parameters block erasure

But if a shared struct wraps a non-copy type,
the outer permission matters --
it distributes into the type parameter
and changes the meaning:

{anchor}`subtyping_non_copy_params_block_erasure`

`shared[d] Box[Data] </: Box[Data]` fails because
the rule distributes: it needs `shared[d] Data <: Data`.
But `Data` is an ordinary struct (not a shared struct),
so `shared[d]` cannot be erased.
Sharing `Data` from a place preserves a dependency that owned `Data` does not have.

## Summary

Subtyping in Dada operates on permissions, not inheritance hierarchies.
Two types are related by subtyping only when they name the same declaration,
and the key question is whether one permission
can stand in for another.

The process:

1. **Decompose** each type into permission + base type
2. **Reduce** each permission to a `RedPerm` (a set of `RedChain`s)
3. **Compare** chain by chain -- every chain in the subtype
   must match some chain in the supertype

Composition flattens through `append_chain`:
copy permissions absorb anything applied to them,
while non-copy permissions concatenate into longer chains.

Shared structs get special treatment:
permissions distribute into type parameters,
and shared structs with no parameters (like `Int`)
make the permission check vacuous.

{{property explicit_ownership_preserves_generic_types}}
