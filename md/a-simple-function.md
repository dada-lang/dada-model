# A simple function

We're going to walk through how the type checker handles a very simple program,
step by step. Here is the complete program:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Point {
            x: Int;
            y: Int;
        }

        class Main {
            fn test(given self) -> Int {
                let p = new Point(22, 44);
                0;
            }
        }
    }
);
```

Nothing very exciting happens here --
we create a `Point` and then return `0`.
But working through this example introduces
the basic machinery that everything else builds on:
the **environment**, **places**, and **types**.

## Grammar declarations

The formal model represents programs using Rust structs
annotated with `#[term]`, a macro from formality-core.
Each `#[term]` struct defines both the abstract syntax
and a textual grammar (the `$`-prefixed patterns).

A class declaration contains a name, an optional class predicate,
and a binder wrapping the fields and methods:

{anchor}`ClassDecl`

A field declaration is a name and a type:

{anchor}`FieldDecl`

A method declaration contains a name and a binder
wrapping the receiver (`this`), parameters, return type, predicates, and body:

{anchor}`MethodDecl`

## The environment

The type checker's job is to walk through each statement in a method body
and track what it knows about each variable.
This information is stored in the **environment** (`Env`),
which maps variables to their types:

{anchor}`Env`

The key field for now is `local_variables`,
which maps each variable to its type.
(We'll explain the other fields as they become relevant.)

When checking `Main::test`, the environment starts out with just the `self` parameter:

| Variable | Type |
| --- | --- |
| `self` | `given Main` |

The `given` permission on `self` means this method takes ownership of `self` --
we'll say more about permissions later.

## Typing `new Point(22, 44)`

The grammar for a `new` expression:

{anchor}`Expr_New`

The expression `new Point(22, 44)` creates a new `Point` instance.
The type checker looks up the class declaration for `Point` and finds two fields:
`x: Int` and `y: Int`.
It checks each argument against the corresponding field type --
`22` against `Int`, `44` against `Int` -- and both succeed.

The resulting type of the expression is `Point`.

## Typing `let p = ...`

The grammar for a `let` statement:

{anchor}`Statement_Let`

A `let` statement evaluates the right-hand side and introduces a new variable
into the environment. After `let p = new Point(22, 44)`, the environment becomes:

| Variable | Type |
| --- | --- |
| `self` | `given Main` |
| `p` | `Point` |

The new variable `p` is bound to the type `Point`.
Simple enough!

## Typing `0`

{anchor}`Expr_Integer`

The final expression in the block is `0`, which is an integer literal with type `Int`.
Since the method's declared return type is `Int`, and `Int` subtypes `Int`,
the method body type-checks successfully.

## What about `p`?

You may have noticed that we never *use* `p`.
We create a `Point`, bind it to `p`, and then ignore it.
The type checker is fine with this!

What actually happens is that when the type checker reaches the `let p = ...` statement,
it computes which variables are **live** after that point --
meaning, which variables are used later in the program.
In this case, `p` is not live after the `let`, because the only thing that follows is `0`,
which doesn't reference `p`.

This notion of **liveness** turns out to be fundamental.
It's what allows the type checker to know when a value can be moved,
when a borrow has expired,
and when a variable can be safely overwritten.
We'll see it in action starting in the next chapter.

## Dropping the expression statement

{anchor}`Statement_Expr`

There is one more subtlety worth mentioning.
The `let p = ...` statement is followed by `0;` -- an expression statement.
When an expression appears as a statement (rather than as the final expression in a block),
its result is evaluated and then **dropped**.

Dropping a value requires permission to do so.
The type checker verifies that the other live variables
in the environment are compatible with dropping the temporary.
For an `Int`, this is trivially true.

This drop check on expression statements
is the same mechanism that will later enforce
that you can't silently discard a value
that someone else has borrowed.
