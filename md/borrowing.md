# Borrowing with `ref`

In the [previous chapter](./giving.md),
we saw how `give` transfers ownership of a value.
But sometimes you want to *use* a value without giving it away.
That's what `ref` is for -- it creates a shared reference
that lets you read the value while the original stays put.

## A simple borrow

Here's a program that creates a `Foo` value,
borrows it with `ref`, and then uses both the original and the borrow:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn test(given self) {
                let foo = new Foo(new Data());
                let bar = foo.ref;
                let i = foo.i.ref;
                bar.give;
                ();
            }
        }
    }
);
```

This works! After `foo.ref`, we can still access `foo.i` --
reading through a shared reference doesn't prevent further reads.
Let's walk through how the type checker handles this.

### Typing `foo.ref`

When the type checker sees `foo.ref`,
it matches the `ref|mut place` rule:

{judgment-rule}`type_expr, ref|mut place`

The rule has three premises:

- **`access_permitted(env, ..., Access::Rf, &place) => env`** --
  Check that borrowing `foo` is permitted.
  This consults the liens on all live variables
  to verify that no conflicting access is active.

- **`env.place_ty(&place)`** --
  Look up the type of `foo`: `Foo`.

- **`access_ty(&env, Access::Rf, &place, ty_place) => ty`** --
  Compute the result type by wrapping the place's typ
  with a `ref` permission.

The `access_ty` judgment for `ref` works like this:

{judgment-rule}`access_ty, ref`

It creates the permission `ref[foo]` and applies it
to the place's type (with the outermost permission stripped).
So `foo.ref` has type `ref[foo] Foo`.

Notice that the permission carries the **place** it was borrowed from.
This is the key idea: `ref[foo]` means
"a shared reference that borrows from `foo`."
The type system uses this to restrict what you can do with `foo`
while the reference is alive.

### How access control works

The interesting premise is `access_permitted`.
How does the type checker decide whether an access is allowed?

When we reach `foo.i.ref` (the third line of the block),
the environment looks like this:

| Variable | Type |
| --- | --- |
| `self` | `given Main` |
| `foo` | `Foo` |
| `bar` | `ref[foo] Foo` |

The type checker needs to confirm that accessing `foo.i`
with `ref` is compatible with all live variables.
The key judgment is `env_permits_access`:

{judgment-rule}`env_permits_access, env_permits_access`

It collects the types of all **live** variables
and checks that each one permits the access.
In our example, `bar` is live (used later by `bar.give`),
so its type `ref[foo] Foo` is checked.

### Liens

To check whether `bar`'s type permits accessing `foo.i`,
the type checker first extracts the **liens** from the type.
Liens are the borrowing constraints embedded in a type:

{anchor}`Lien`

A `Lien::Rf(place)` means "a read-only borrow of `place`."
A `Lien::Mt(place)` means "a mutable borrow of `place`."

The `liens` judgment extracts liens from permissions:

{judgment-rule}`liens, perm-shared`

For `Perm::Rf(places)`, it creates a `Lien::Rf` for each place.
So `ref[foo] Foo` yields the lien `Lien::Rf(foo)`.

### The `ref'd` rule

Once the liens are extracted, each lien is checked against the access.
For a `Lien::Rf`, the `ref'd` rule delegates to `ref_place_permits_access`:

{judgment-rule}`lien_permit_access, ref'd`

The rules for what a `ref` lien permits are:

{judgment}`ref_place_permits_access`

Three rules:

- **`share-share`**: A ref lien permits any `ref` or `share` access
  to *any* place -- reading is always compatible with reading.

- **`share-mutation`**: A ref lien permits `mut` or `drop` access
  only to places **disjoint** from the borrowed place.
  You can mutate something unrelated, but not the borrowed data.

- **`share-give`**: A ref lien permits `give` access
  only to places that are **disjoint from or a prefix of** the borrowed place.
  (Giving away the prefix cancels the borrow.)

### Applying it to our example

When checking `foo.i.ref` against the lien `Lien::Rf(foo)`:

- The access is `ref` (Access::Rf)
- The `share-share` rule fires -- ref is always compatible with ref
- Access is permitted

That's why the program works.

## Mutation through a ref is an error

A ref creates a read-only borrow.
If you try to mutably borrow a field while a ref is active,
the type checker rejects it:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn test(given self) {
                let foo = new Foo(new Data());
                let bar = foo.ref;
                let i = foo.i.mut;
                bar.give;
                ();
            }
        }
    },
    r#"the rule "share-mutation" at (*) failed"#,
    "`place_disjoint_from(&accessed_place, &shared_place)`",
    "&accessed_place = foo . i",
    "&shared_place = foo",
);
```

Here the access is `mut` (Access::Mt),
so the `share-mutation` rule applies.
It requires `foo.i` to be **disjoint** from the borrowed place `foo`.
But `foo.i` is a sub-place of `foo` -- not disjoint -- so the check fails.

This is the fundamental guarantee of shared references:
while a ref to `foo` exists, you cannot mutate `foo` or any of its fields.

## Giving a field away while ref'd is an error

Similarly, you can't give away a field of a ref'd value:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn test(given self) {
                let foo = new Foo(new Data());
                let bar = foo.ref;
                let i = foo.i.give;
                bar.give;
                ();
            }
        }
    },
    r#"the rule "share-give" at (*) failed"#,
    "`place_disjoint_from_or_prefix_of(&accessed_place, &shared_place)`",
    "&accessed_place = foo . i",
    "&shared_place = foo",
);
```

The `share-give` rule requires the accessed place to be
disjoint from *or a prefix of* the borrowed place.
`foo.i` is neither disjoint from nor a prefix of `foo`
(it's a *suffix*), so the check fails.

Why the "prefix" exception?
Giving away `foo` itself would cancel the borrow --
the reference can't outlive what it borrows.
But giving away `foo.i` would leave `foo` in a partially-moved state
while `bar` still refers to it.

## Liveness cancels restrictions

Liens only matter while the borrowing variable is **live** --
that is, while later code might use it.
Once the borrower dies, its restrictions vanish:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn test(given self) {
                let foo = new Foo(new Data());
                let bar = foo.mut;
                let i = foo.i.ref;
                ();
            }
        }
    }
);
```

Wait -- `bar` is a *mutable* borrow of `foo`,
and we're taking a ref of `foo.i`!
Normally a `mut` lien blocks all access
(even reads) to the borrowed place and its sub-places.
But `bar` is never used after the `let i = ...` line.

When the type checker reaches `foo.i.ref`,
it collects the types of all **live** variables.
Since `bar` is not live (nothing references it afterward),
its type `mut[foo] Foo` is not in the checked set.
No liens, no restrictions, access is permitted.

This is analogous to Rust's non-lexical lifetimes (NLL) --
borrows end when the reference is last used,
not when it goes out of scope.

## Mutable borrows are more restrictive

For comparison, here's how `mut` liens differ from `ref` liens.
A `mut` lien blocks *all* access (even reads) to overlapping places:

{judgment}`mut_place_permits_access`

- **`lease-mutation`**: A mut lien permits `share`, `ref`, `mut`, or `drop`
  access only to places **disjoint** from the leased place.
  No reads, no shares, no further borrows of the leased data.

- **`lease-give`**: A mut lien permits `give` access
  only to places that are **disjoint from or a prefix of** the leased place.

That's why this fails:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn test(given self) {
                let foo = new Foo(new Data());
                let bar = foo.mut;
                let i = foo.i.ref;
                bar.give;
                ();
            }
        }
    },
    r#"the rule "lease-mutation" at (*) failed"#,
    "`place_disjoint_from(&accessed_place, &leased_place)`",
    "&accessed_place = foo . i",
    "&leased_place = foo",
);
```

`bar` is live (used by `bar.give`),
so its `Lien::Mt(foo)` is active.
The `lease-mutation` rule requires `foo.i` to be disjoint from `foo` --
it isn't, so the access is rejected.

## Disjoint access is fine

Both `ref` and `mut` liens permit access to **disjoint** places.
Borrowing `foo` doesn't prevent you from touching unrelated data:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self) {
                let foo = new Data();
                let other = new Data();
                let bar = foo.ref;
                other.give;
                bar.give;
            }
        }
    }
);
```

`bar` borrows `foo`, creating the lien `Lien::Rf(foo)`.
When we give `other`, the `share-give` check asks:
is `other` disjoint from `foo`?  Yes -- they're different variables.
Access is permitted.

## Transitive restrictions

Liens compose transitively.
If you borrow from a borrow, the original restrictions still apply:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn test(given self) {
                let p = new Foo(new Data());
                let q = p.mut;
                let r = q.ref;
                let i = p.i.ref;
                r.give;
                ();
            }
        }
    },
    r#"the rule "lease-mutation" at (*) failed"#,
    "`place_disjoint_from(&accessed_place, &leased_place)`",
    "&accessed_place = p . i",
    "&leased_place = p",
);
```

Here `q` has type `mut[p] Foo` and `r` has type `ref[q] Foo`.
When we try `p.i.ref`, the type checker checks `r`'s type.
The liens of `ref[q] Foo` include `Lien::Rf(q)` --
but also the liens from looking up `q`'s type `mut[p] Foo`,
which yields `Lien::Mt(p)`.

So even though `r` only directly references `q`,
the chain of borrows transitively propagates the restriction back to `p`.
The `lease-mutation` rule blocks `p.i.ref` because
`p.i` is not disjoint from `p`.

Note that `q` itself is dead here (nothing uses `q` after `let r`).
But the *type* of `r` still records the transitive dependency on `p`,
and `r` is live.

## Summary

| Access mode | Creates permission | Creates lien | Permits reads of borrowed place? | Permits mutations of borrowed place? |
| --- | --- | --- | --- | --- |
| `ref` | `ref[place]` | `Lien::Rf(place)` | Yes | No |
| `mut` | `mut[place]` | `Lien::Mt(place)` | No | No |

The access control system enforces these constraints through three mechanisms:

1. **Liens** extracted from the types of live variables
2. **Disjointness checks** that determine whether two places overlap
3. **Liveness** that automatically cancels restrictions when the borrower is no longer used
