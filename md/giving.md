# Giving

In Dada, values are accessed through **place expressions** like `p.x.give`.
The trailing keyword (here, `give`) determines what kind of access is being performed.
The access modes are:

| Access | Meaning |
| --- | --- |
| `give` | Give ownership of the value (move) |
| `ref` | Borrow a shared reference |
| `mut` | Borrow a mutable reference |
| `share` | Create a shared copy |

We'll start with `give`, which is the most fundamental.

## Giving a value

If you are familiar with Rust,
`give` is analogous to a move.
When you give a value, you transfer ownership of it.
The following program creates a `Data` value and gives it away as the return value:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self) -> Data {
                let d = new Data();
                d.give;
            }
        }
    }
);
```

## Giving a value twice is an error

Once a value has been given away, it is gone.
Trying to use it again is an error:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Main {
            fn test(given self) -> Data {
                let d = new Data();
                d.give;
                d.give;
            }
        }
    },
    r#"the rule "give" at (*) failed"#,
    "`!live_after.is_live(&place)`",
    "&place = d",
);
```

This is the same principle as Rust's move semantics --
after a move, the original binding is no longer valid.

## Giving a field

You can give individual fields from a class instance.
After giving a field, that specific field is no longer available,
but other fields remain accessible:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Pair {
            a: Data;
            b: Data;
        }

        class Main {
            fn test(given self) -> Data {
                let p = new Pair(new Data(), new Data());
                p.a.give;
                p.b.give;
            }
        }
    }
);
```

## Giving a field and then the whole value is an error

If you give away a field, the whole value is now incomplete,
so you can't give the whole thing:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Pair {
            a: Data;
            b: Data;
        }

        class Main {
            fn test(given self) -> Pair {
                let p = new Pair(new Data(), new Data());
                p.a.give; // <-- Error! Can't give `p.a` when `p` will be used later.
                p.give;
            }
        }
    },
    r#"the rule "give" at (*) failed"#,
    "`!live_after.is_live(&place)`",
    "&place = p . a",
);
```

Conversely, if you give the whole value, you can't access its fields afterward:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Pair {
            a: Data;
            b: Data;
        }

        class Main {
            fn test(given self) -> Data {
                let p = new Pair(new Data(), new Data());
                p.give;   // <-- Error! Can't give `p` when `p.a` will be used later.
                p.a.give;
            }
        }
    },
    r#"the rule "give" at (*) failed"#,
    "`!live_after.is_live(&place)`",
    "&place = p",
);
```

## Structs are copyable

Unlike class instances, struct values are always shared and can be given multiple times.
`Int` is a built-in struct, so this works fine:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Main {
            fn test(given self) -> Int {
                let x = 22;
                x.give;
                x.give;
            }
        }
    }
);
```

This is because struct types have the `shared` class predicate,
which makes them copyable -- giving a struct value copies it rather than moving it.
