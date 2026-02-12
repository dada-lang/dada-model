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

## How type checking begins

Type checking starts at `check_program`,
which iterates over each class declaration in the program:

{anchor}`check_program`

For each class, it checks the fields and then each method.
Here is `check_method`, where the environment gets set up:

{anchor}`check_method`

The key lines for our example are the ones that build the environment.
The method declaration for `test` specifies `given self`,
so `check_method` computes the type `given Main`
and pushes it into the environment as `self`.
If there were other parameters, they'd be pushed too.

Once the environment is ready, `check_method` calls `check_body`:

{anchor}`check_body`

Two things to note here.
First, `live_after` starts as the empty set --
nothing is live after the method body returns.
Second, `can_type_expr_as` checks that the body expression
can be typed as the declared return type (`Int`).
This is where we cross from ordinary Rust code
into **judgment functions** -- the inference rules
that define the type system.

## Judgment functions

A judgment function is defined with the `judgment_fn!` macro.
Each rule in the judgment has **premises** above the line
and a **conclusion** below.
The rule applies when all the premises can be satisfied.

The body of a method is a block, so `type_expr` dispatches to `type_block`:

{judgment-rule}`type_block, place`

A block is just a sequence of statements,
so this delegates to `type_statements`,
which walks through statements one at a time:

{judgment-rule}`type_statements_with_final_ty, cons`

The type of the last statement becomes the type of the block.

Notice the first premise: `live_after.before(&statements)`.
Every judgment rule in the type system carries a `live_after` parameter --
the set of variables that are **live** (i.e., used later in the program).
In this chapter, nothing interesting happens with liveness
because we never use our variables again.
We'll explain liveness in detail in the [Giving](./giving.md) chapter,
where it determines whether a value is moved or copied.

## Typing `let p = new Point(22, 44)`

The `let` statement is handled by this rule:

{judgment-rule}`type_statement, let`

Walking through the premises one by one:

- **`type_expr(env, live_after.overwritten(&id), ...)`** --
  Type the right-hand side expression (`new Point(22, 44)`).
  The `live_after.overwritten(&id)` removes `p` from the live set,
  since `p` doesn't exist yet while the RHS is being evaluated.

- **`push_local_variable(&id, ty)`** --
  Add `p` to the environment with the type inferred from the RHS.

- **`with_in_flight_stored_to(&id)`** --
  Record that the result of the expression is now stored in `p`.
  (We'll explain "in-flight" values in a later chapter --
  for now, just think of it as "the result of the expression
  flows into the variable".)

### Typing `new Point(22, 44)`

The `new` expression is typed by this rule:

{judgment-rule}`type_expr, new`

Walking through this for `new Point(22, 44)`:

1. Look up the class `Point` and find its fields: `x: Int`, `y: Int`.
2. Check the argument count matches (2 = 2).
3. Create a temporary variable to represent the object under construction.
4. Type each argument against the corresponding field type
   via `type_field_exprs_as` -- `22` against `Int`, `44` against `Int`.
   Both succeed via the integer typing rule:

{judgment-rule}`type_expr, constant`

The resulting type of the `new` expression is `Point`.

### After the `let`

After typing `let p = new Point(22, 44)`, the environment becomes:

| Variable | Type |
| --- | --- |
| `self` | `given Main` |
| `p` | `Point` |

## Typing the return expression `0`

The final statement in the block is `0` -- an expression statement.
It is typed by this rule:

{judgment-rule}`type_statement, expr`

The expression `0` has type `Int` (by the "constant" rule shown above).
Since this is an expression statement, the result is **dropped** --
the rule checks that both the environment and the type
permit dropping the temporary value.
For `Int`, this is trivially true.

The type of the last statement (`Int`) becomes the type of the block.
Back in `check_body`, this is checked against the declared return type `Int`,
and the method type-checks successfully.

## What about `p`?

You may have noticed that we never *use* `p`.
We create a `Point`, bind it to `p`, and then ignore it.
The type checker is fine with this --
`p` is never referenced after the `let`,
so it's not in the live set and the type checker simply ignores it.

In the next chapter, we'll see what happens
when variables *are* live -- and how liveness
determines whether a value is moved or copied.
