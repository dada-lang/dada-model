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

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self, d: given Data) {
                let s: shared Data = new Data().share;
                let r: ref[d] Data = s.give;
                ();
            }
        }
    }
);
```

The value `s` has type `shared Data`.
The target `r` expects `ref[d] Data`.
Since `shared <: ref[d]`, this works.

### `ref[d]` is NOT `<: shared`

The reverse doesn't hold --
a borrow can't become ownership:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Main {
            fn test(given self, d: given Data) {
                let r: ref[d] Data = d.ref;
                let s: shared Data = r.give;
                ();
            }
        }
    },
    r#"predicates.rs"#,
);
```

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

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self, d: given Data) {
                let s: shared Data = new Data().share;
                let r: shared mut[d] Data = s.give;
                ();
            }
        }
    }
);
```

### `ref[d] <: shared mut[d]`

A reference can stand in for a shared lease
from the same place:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self, d: given Data) {
                let r: ref[d] Data = d.ref;
                let sm: shared mut[d] Data = r.give;
                ();
            }
        }
    }
);
```

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

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Main {
            fn test(given self, d: given Data) {
                let p: mut[d] Data = d.mut;
                let sm: shared mut[d] Data = p.ref;
                let r: ref[d] Data = sm.give;
                ();
            }
        }
    },
    r#"predicates.rs"#,
);
```

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

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self) {
                let d: shared Data = new Data().share;
                let r = d.ref;
                let s: shared Data = r.give;
                ();
            }
        }
    }
);
```

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

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self) {
                let d: given Data = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] mut[d] Data = p.ref;
                ();
            }
        }
    }
);
```

Here `p.ref` creates `ref[p] mut[d] Data` --
a chain of two links.
The permission records that you borrowed from `p`,
which itself was leased from `d`.

What happens when you want to *use* this value
depends on whether `p` is still alive --
and that's a story for a later chapter on liveness
and permission reduction.

## `mut[d]` is not copy

It's worth noting what's NOT in the copy family.
A mutable lease `mut[d]` is NOT copy --
it provides exclusive mutable access,
which can't be duplicated:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Main {
            fn test(given self, d: given Data) {
                let p: mut[d] Data = d.mut;
                let q: ref[d] Data = p.give;
                ();
            }
        }
    },
    r#"predicates.rs"#,
);
```

`mut[d] </: ref[d]` --
a lease grants exclusive mutation rights,
while a reference only grants shared read access.
These are incomparable: neither is a subtype of the other.

Similarly, `given` (unique ownership) is not comparable
to any of the copy permissions:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Main {
            fn test(given self, d: given Data) {
                let s: shared Data = d.give;
                ();
            }
        }
    },
    r#"predicates.rs"#,
);
```

`given </: shared` --
unique ownership and shared ownership
represent fundamentally different memory models.

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
