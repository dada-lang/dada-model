# Liveness and cancellation

In the previous sub-chapters,
we saw how permissions are compared structurally --
place ordering and the copy permission hierarchy.
But those rules assume all borrowed places are still alive.

What happens when a borrowed place is **dead** --
no longer used by later code?

Dead links in a `RedChain` can be **cancelled** or **promoted**,
which enables subtyping relationships
that wouldn't hold for live links.
This is Dada's equivalent of Rust's non-lexical lifetimes (NLL) --
borrows end when the reference is last used,
not when it goes out of scope.

## A motivating example: re-borrowing

Consider a function that re-borrows a lease:

{anchor}`liveness_dead_mut_cancels`

Here's what happens step by step:

1. `d` is created with type `given Data`
2. `p: mut[d] Data` -- a mutable lease of `d`
3. `q: mut[p] Data` -- a mutable lease of `p` (a re-borrow)
4. `r: mut[d] Data` -- we want `q.give` to have type `mut[d] Data`

The expression `q.give` has type `mut[p] Data`.
But `r` expects `mut[d] Data`.
How can `mut[p] mut[d]` become `mut[d]`?

When we reduce `mut[p]`, the permission for `q.give`,
we get the chain `[Mtd(p)]` --
`p` is dead because `q.give` is the last expression,
and `p` is never used again.
Chain expansion follows `p`'s type (`mut[d] Data`),
appending `Mtl(d)` to get `[Mtd(p), Mtl(d)]`.

The target `mut[d]` reduces to `[Mtl(d)]`.

Comparing `[Mtd(p), Mtl(d)]` vs `[Mtl(d)]`:
the **cancellation rule** fires --
since `p` is dead, the `Mtd(p)` link is dropped,
and comparison continues with the tail `[Mtl(d)]` vs `[Mtl(d)]`,
which succeeds.

### But not when the place is live

If `p` is still used after the assignment, cancellation is blocked:

{anchor}`liveness_live_mut_no_cancel`

Here `p` appears in `p.give.read[...]()` after `q.give`,
so `p` is **live** at the point where `q.give` is evaluated.
The chain becomes `[Mtl(p), Mtl(d)]` (live, not dead) --
and there is no rule to cancel a live `Mtl` link.
The assignment to `r: mut[d] Data` fails.

## The two cancellation operations

Dead links are resolved by two rules in `red_chain_sub_chain`:

### Cancellation: dropping a dead `mut` link

{judgment-rule}`red_chain_sub_chain, (mut-dead::P) vs Q ~~> (P) vs Q`

When the chain starts with `Mtd(place)` (a dead mutable lease),
the rule drops it and continues comparing the tail against the target.

Three conditions must hold:

1. The place must be **dead** (encoded by the `Mtd` variant)
2. The type of the dead place must be **shareable** --
   `prove_is_shareable(env.place_ty(place_dead))`
3. The **tail** must be mut-based --
   `prove_is_mut(tail_a)`

The shareable check ensures it's safe to silently release the lease.
The tail check ensures we're cancelling a lien on top of another lease,
not an owned permission.

### Promotion: converting a dead `ref` to `shared`

{judgment-rule}`red_chain_sub_chain, (ref-dead::P) vs Q ~~> (shared::P) vs Q`

When the chain starts with `Rfd(place)` (a dead reference),
the rule replaces it with `Shared`
and continues comparing.

This reflects the fact that once the borrowed place is dead,
the reference effectively becomes shared --
no one can invalidate it through the original place anymore.

Here's an example of promotion in action:

{anchor}`liveness_dead_ref_promotes`

The expression `q.give` has type `ref[p] mut[d] Data`.
The target `r` expects `shared mut[d] Data`.
Since `p` is dead, the chain `[Rfd(p), Mtl(d)]`
promotes `Rfd(p)` to `Shared`,
giving `[Shared, Mtl(d)]` which matches `shared mut[d]`.

If `p` were still live, promotion wouldn't happen:

{anchor}`liveness_live_ref_no_promote`

With `p` live, the chain is `[Rfl(p), Mtl(d)]` --
the `Rfl` variant has no promotion rule,
and the comparison fails.

## A practical pattern: re-borrowing in functions

Liveness-based cancellation enables a common pattern --
re-borrowing inside a function and returning the result:

{anchor}`liveness_return_cancels`

The parameter `d: mut[self] Data` is a mutable lease from `self`.
Inside the function, `d.mut` creates `mut[d] Data` --
a re-borrow. When we return `p.give`,
its type is `mut[d] Data`.
The return type expects `mut[self] Data`.

Since `d` is dead at the return point
(it's a parameter that's not used after `p.give`),
the `Mtd(d)` link cancels,
and the chain collapses to `mut[self]`.

Without liveness-based cancellation,
re-borrowing would be useless --
you could never return a value
that was transiently borrowed through a local.

## What cancellation cannot do

Not all dead links can be resolved.
There are important limits on when cancellation and promotion apply.

### Shared-to-leased conversion is blocked

Cancellation can resolve links within a permission chain,
but it cannot change the *nature* of a permission
from shared (copy) to leased (exclusive):

{anchor}`liveness_ref_shared_no_cancel`

The expression `q.give` has type `ref[p] mut[d] Data`.
Even though `p` is dead,
the chain `[Rfd(p), Mtl(d)]` cannot become `[Mtl(d)]`.

Why? Promotion converts `Rfd(p)` to `Shared`,
giving `[Shared, Mtl(d)]` -- a shared lease.
But `mut[d]` reduces to `[Mtl(d)]` -- an exclusive lease.
`shared mut[d]` is not a subtype of `mut[d]`.

This reflects a real safety invariant:
a reference (even a dead one) was shared --
multiple copies may exist.
You can't recover exclusive access
from something that was shared.

### Multi-place permissions: all places must be dead

When a permission mentions multiple places,
like `ref[p, q]`, reduction produces one chain per place.
For cancellation to resolve all of them,
**every** place must be dead:

{anchor}`liveness_both_places_dead_cancels`

Both `p` and `q` are dead at the point of `r.give`,
so both `Rfd(p)` and `Rfd(q)` chains can be resolved.

But if even one place is still live:

{anchor}`liveness_all_places_must_be_dead`

Here `q` is used after `r.give` (in `q.give`),
so `q` is live at the point where `r.give` is evaluated.
The chain `Rfl(q)` (live, not dead) has no cancellation rule,
and the comparison fails --
even though `p` is dead and its chain could be resolved.

## How liveness is computed

Liveness is computed **backwards** through the program.
Starting from the end of the function body
(where nothing is live),
the analysis walks statements in reverse,
tracking which places are accessed or traversed.

A place is **live** if:
- It or any overlapping place is accessed later, or
- It is a prefix of a place that gets assigned to later

A place is **dead** if it is not live --
no future code reads from it or any of its sub-places.

This backward analysis means liveness depends on
*what comes after* a given point in the program.
The same variable can be live at one point
and dead at another.

The type system threads `LivePlaces` through the checking process:
when `sub_perms` is called, it receives the set of places
that are live **after** the current expression.
This is what determines whether a `ref[d]` or `mut[d]`
reduces to the live variant (`Rfl`/`Mtl`)
or the dead variant (`Rfd`/`Mtd`).

## Summary

| Operation | Applies to | Result | Conditions |
| --- | --- | --- | --- |
| Cancellation | `Mtd(place)` | Drop the link | Place dead, type shareable, tail is mut |
| Promotion | `Rfd(place)` | Replace with `Shared` | Place dead, type shareable, tail is mut |

Key constraints:
- Only dead links can be cancelled or promoted
- The dead place's type must be shareable
- The tail of the chain must be mut-based
- Shared-to-leased conversion is never possible
- Multi-place permissions require all places to be dead
- Liveness is computed backwards from end of function
