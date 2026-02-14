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
the **environment**, **places**, **types**,
and -- most importantly -- how the type checker
is structured as a set of **judgment functions**
with **inference rules**.

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

## Judgments and inference rules

The type system is defined as a collection of **judgment functions**.
Each judgment function is defined with the `judgment_fn!` macro
and contains one or more **inference rules**.
An inference rule has **premises** above a horizontal line
and a **conclusion** below it.
The conclusion holds when all the premises are satisfied.

For example, an inference rule with the conclusion
`check_program(program) => ()` means
"the program type-checks successfully."
The premises above the line specify what must be true
for that conclusion to hold.

## How type checking begins

Type checking begins with the `check_program` judgment,
which checks that every declaration in the program is well-formed:

{judgment-rule}`check_program, check_program`

The sole premise uses `for_all` to require that
`check_decl` succeeds for each declaration.
In our example, the program has two declarations (`Point` and `Main`),
so the premise is satisfied when both classes check successfully.

For each class, `check_class` checks the fields and then each method.
Let's look at the rule for `check_method`:

{judgment-rule}`check_method, check_method`

For our example, the method declaration for `test` specifies `given self`,
so the premises compute the type `given Main`
and push it into the environment as `self`.
If there were other parameters, they'd be pushed too.
Once the environment is ready,
the final premise invokes the `check_body` judgment:

{judgment-rule}`check_body, block`

The "block" rule applies to our example
(the "trusted" rule handles built-in methods with no body).
Its premises initialize `live_after` to the empty set --
nothing is live after the method body returns --
and then require that `can_type_expr_as` succeeds,
checking that the body can be typed as the declared return type (`Int`).

## Typing a block

The body of a method is a block expression,
so `type_expr` dispatches to `type_block`:

{judgment-rule}`type_block, place`

A block is a sequence of statements,
so this delegates to `type_statements`,
which walks through statements one at a time:

{judgment-rule}`type_statements_with_final_ty, cons`

The type of the last statement becomes the type of the block.

Notice the first premise: `live_after.before(&statements)`.
Every judgment in the type system carries a `live_after` parameter --
the set of variables that are **live** (i.e., used later in the program).
In this chapter, nothing interesting happens with liveness
because we never use our variables again.
We'll explain liveness in detail in the [Giving](./giving.md) chapter,
where it determines whether a value is moved or copied.

## Typing `let p = new Point(22, 44)`

The `let` statement is handled by this rule:

{judgment-rule}`type_statement, let`

The rule has three premises:

- **`type_expr(env, live_after.overwritten(&id), ...) => (env, ty)`** --
  Type the right-hand side expression (`new Point(22, 44)`)
  and produce its type `ty`.
  The `live_after.overwritten(&id)` removes `p` from the live set,
  since `p` doesn't exist yet while the RHS is being evaluated.

- **`env.push_local_variable(&id, ty)`** --
  Add `p` to the environment with the type produced by the first premise.

- **`env.with_in_flight_stored_to(&id)`** --
  Record that the result of the expression is now stored in `p`.
  (We'll explain "in-flight" values in a later chapter --
  for now, just think of it as "the result of the expression
  flows into the variable".)

### Typing `new Point(22, 44)`

The `new` expression is typed by the following rule:

{judgment-rule}`type_expr, new`

The premises require:

1. Looking up the class `Point` to find its fields: `x: Int`, `y: Int`.
2. Checking that the argument count matches the field count (2 = 2).
3. Creating a temporary variable to represent the object under construction.
4. Invoking `type_field_exprs_as` to type each argument
   against the corresponding field type --
   `22` against `Int`, `44` against `Int`.
   Both succeed via the integer typing rule:

{judgment-rule}`type_expr, constant`

The "constant" rule has no premises --
the conclusion `type_expr(env, _, Expr::Integer(_)) => (env, Ty::int())`
holds unconditionally.
Any integer literal has type `Int`.

The conclusion of the "new" rule gives us the type `Point`.

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

The first premise types the expression `0`,
yielding type `Int` (by the "constant" rule shown above).
The remaining premises check that both the environment and the type
permit **dropping** the temporary value.
For `Int`, dropping is trivially permitted.

The type of the last statement (`Int`) becomes the type of the block.
Back in `check_body`, the `can_type_expr_as` premise
checks this against the declared return type `Int` --
subtyping succeeds, and the method type-checks successfully.

## What about `p`?

You may have noticed that we never *use* `p`.
We create a `Point`, bind it to `p`, and then ignore it.
The type checker is fine with this --
`p` is never referenced after the `let`,
so it's not in the live set and the type checker simply ignores it.

In the next chapter, we'll see what happens
when variables *are* live -- and how liveness
determines whether a value is moved or copied.
