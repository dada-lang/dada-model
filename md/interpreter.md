# Running a program

The previous chapters showed how the type checker verifies that a program
is well-formed.
But checking types is only half the story --
we also want to *run* programs.
The **interpreter** takes a type-checked program
and evaluates it, producing a result.

Here is a simple program that creates a `Point` and returns it:

```rust
# extern crate dada_model;
dada_model::assert_interpret!(
    {
        class Point {
            x: Int;
            y: Int;
        }

        class Main {
            fn main(given self) -> Point {
                let p = new Point(22, 44);
                p.give;
            }
        }
    },
    "Point { flag: Given, x: 22, y: 44 }"
);
```

The interpreter starts by creating a `Main()` instance
and calling its `main` method.
The method creates a `Point`, gives it away as the return value,
and the interpreter displays the result: `Point { flag: Given, x: 22, y: 44 }`.
The `flag: Given` tells us this is a uniquely owned value.

## The memory model

The interpreter models memory as a collection of **allocations**.
Each allocation is a flat array of **words** --
there are no pointers between fields,
no type tags in memory,
and no named field maps.
This mirrors how a real machine represents values.

An `Alloc` is a flat vector of words:

{anchor}`Alloc`

Each word is one of:

{anchor}`Word`

- **`Int(n)`** -- an integer value.
- **`Flags(f)`** -- a permission flag for unique objects.
- **`Uninitialized`** -- the slot has been moved or cleared.

The `Flags` enum tracks the permission state of a unique object:

{anchor}`Flags`

- **`Given`** -- the value is uniquely owned.
- **`Shared`** -- the value has been shared (copyable).
- **`Borrowed`** -- the value is a read-only reference copy.
- **`Uninitialized`** -- the value has been moved away.

A `Pointer` identifies a position within an allocation:

{anchor}`Pointer`

### Object layout

Unique classes (regular `class` and `guard class`) are laid out
with a flags word followed by their fields:

```text
+-------------------+
| Flags(Given)      |   ← flags word
| field 0 words...  |
| field 1 words...  |
| ...               |
+-------------------+
```

Shared classes (`struct class`) have no flags word --
they are always copyable, so no permission tracking is needed:

```text
+-------------------+
| field 0 words...  |
| field 1 words...  |
| ...               |
+-------------------+
```

An `Int` is a single word `[Int(n)]`.
A unit value `()` is an empty allocation (zero words).

### Types flow through evaluation, not memory

The interpreter does **not** store type information in allocations.
Memory is just words -- the type exists in the evaluator's head.
A `TypedValue` pairs a pointer with the type needed to interpret it:

{anchor}`TypedValue`

The stack frame maps variables to `TypedValue`s,
so we always know both *where* a value lives and *what type* it is:

{anchor}`StackFrame`

## The interpreter and stack frames

The interpreter holds a reference to the program,
a type system environment (used to check whether types are copyable),
and the collection of allocations:

{anchor}`Interpreter`

Each method call creates a `StackFrame`
that maps variable names to typed value pointers.

## Walking through evaluation

Let's trace through the example above step by step.

### Entry point

The interpreter begins by instantiating `Main()` --
a unique class with no fields, so its allocation is just a flags word --
then calling `main` on it.
The stack frame for `main` starts with `self` bound to the `Main` allocation:

```text
allocs: [ [Flags(Given)] ]
stack:  { self → (alloc 0, Main) }
```

### `let p = new Point(22, 44)`

The `new` expression evaluates each field argument
(creating temporary allocations for each integer),
then builds a flat allocation for the `Point`:

```text
allocs: [ [Flags(Given)],     ← Main (alloc 0)
          [Int(22)],           ← temp for 22 (alloc 1)
          [Int(44)],           ← temp for 44 (alloc 2)
          [Flags(Given), Int(22), Int(44)] ]  ← Point (alloc 3)
stack:  { self → (alloc 0, Main), p → (alloc 3, Point) }
```

Alloc 3 holds a `Point` with its flags word at offset 0,
`x` at offset 1, and `y` at offset 2.
To access `p.x`, the interpreter uses the type `Point`
to compute that field `x` starts at offset 1.

### `p.give`

The `give` access mode copies the words to a new allocation
and marks the source's flags as `Uninitialized`.
Since `p` is the last statement, this is the return value:

```text
allocs: [ ...,
          [Flags(Uninitialized), Int(22), Int(44)],  ← alloc 3 (moved)
          [Flags(Given), Int(22), Int(44)] ]          ← alloc 4 (copy)
```

The method returns alloc 4 -- a fresh `Point` with copied words.
Displayed: `Point { flag: Given, x: 22, y: 44 }`.

## Arithmetic

The interpreter supports integer arithmetic:

```rust
# extern crate dada_model;
dada_model::assert_interpret!(
    {
        class Main {
            fn main(given self) -> Int {
                let x = 10;
                let y = 20;
                x.give + y.give;
            }
        }
    },
    "30"
);
```

## Method calls

Methods can call other methods on objects they receive.
The interpreter uses the receiver's **type** (not the memory contents)
to resolve which class and method to call,
creates a new stack frame, and evaluates the body:

```rust
# extern crate dada_model;
dada_model::assert_interpret!(
    {
        class Adder {
            a: Int;
            b: Int;

            fn sum(given self) -> Int {
                self.a.give + self.b.give;
            }
        }

        class Main {
            fn main(given self) -> Int {
                let adder = new Adder(3, 4);
                adder.give.sum();
            }
        }
    },
    "7"
);
```

When the interpreter encounters `adder.give.sum()`,
it first evaluates the receiver `adder.give` --
copying the `Adder`'s words to a new allocation.
Then it uses the type `Adder` to look up `sum`,
creates a stack frame with `self` bound to the copied adder,
and evaluates the body.

## Access modes at runtime

The type checker verifies that access modes are used correctly.
The interpreter executes them:

| Access | Runtime behavior |
| --- | --- |
| `give` | Copy the words, set source flags to `Uninitialized` |
| `ref` | Copy with the flags word set to `Borrowed` |
| `mut` | Not yet implemented |
| `share` | Copy with the flags word set to `Shared` |

### Ref produces a copy

A `ref` access creates an independent copy of the data,
tagged with the `Borrowed` flag.
Because it's a copy, the original remains accessible:

```rust
# extern crate dada_model;
dada_model::assert_interpret!(
    {
        class Data { }

        class Pair {
            a: Data;
            b: Data;
        }

        class Main {
            fn main(given self) -> Data {
                let p = new Pair(new Data(), new Data());
                let r = p.ref;
                p.a.give;
            }
        }
    },
    "Data { flag: Given }"
);
```

Here `p.ref` creates a copy of the `Pair` and its fields.
After that, we can still `give` away `p.a` --
the ref copy is independent.

## Conditionals

The `if` expression evaluates a condition
and executes one of two branches.
The interpreter treats `0` as false and any other integer as true.
Since `if` returns unit, we use assignment
to communicate a result out:

```rust
# extern crate dada_model;
dada_model::assert_interpret!(
    {
        class Main {
            fn main(given self) -> Int {
                let result = 0;
                if 1 { result = 42; } else { result = 0; };
                result.give;
            }
        }
    },
    "42"
);
```

```rust
# extern crate dada_model;
dada_model::assert_interpret!(
    {
        class Main {
            fn main(given self) -> Int {
                let result = 0;
                if 0 { result = 42; } else { result = 99; };
                result.give;
            }
        }
    },
    "99"
);
```
