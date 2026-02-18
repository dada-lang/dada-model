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
    "Point { flag: Owned, x: 22, y: 44 }"
);
```

The interpreter starts by creating a `Main()` instance
and calling its `main` method.
The method creates a `Point`, gives it away as the return value,
and the interpreter displays the result: `Point { flag: Owned, x: 22, y: 44 }`.
The `flag: Owned` tells us this is a uniquely owned value.

## The value model

Every value the interpreter creates is stored in a flat array of slots.
A `Value` is just an index into this array:

{anchor}`Value`

Each slot holds a `ValueData`:

{anchor}`ValueData`

- **`Int(n)`** -- an integer.
- **`Object(data)`** -- a class instance with a flag, class name, and field map.
- **`Pointer(target)`** -- indirection to another slot (used for mutable borrows).
- **`Uninitialized`** -- the slot has been moved or cleared.

An object carries an `ObjectFlag` that tracks its permission state:

{anchor}`ObjectFlag`

- **`Owned`** -- the value is uniquely owned.
- **`Shared`** -- the value has been shared (copyable).
- **`Ref`** -- the value is a read-only reference copy.

Object data includes the class name and a map from field names to value slots:

{anchor}`ObjectData`

## The interpreter and stack frames

The interpreter holds a reference to the program,
a type system environment (used to check whether types are copyable),
and the flat array of value slots:

{anchor}`Interpreter`

Each method call creates a `StackFrame`
that maps variable names to value slots:

{anchor}`StackFrame`

## Walking through evaluation

Let's trace through the example above step by step.

### Entry point

The interpreter begins by instantiating `Main()` --
an object with no fields --
then calling `main` on it.
The stack frame for `main` starts with `self` bound to the `Main` object:

```text
values: [Main]
stack:  { self → 0 }
```

### `let p = new Point(22, 44)`

The `new` expression evaluates each field argument,
allocates an object, and stores field values:

```text
values: [Main, 22, 44, Point { x → 1, y → 2 }]
stack:  { self → 0, p → 3 }
```

Slot 3 holds a `Point` object whose `x` field points to slot 1 (the integer 22)
and whose `y` field points to slot 2 (the integer 44).

### `p.give`

The `give` access mode copies the value out of the slot
and marks the source as uninitialized.
Since `p` is the last statement, this is the return value:

```text
values: [Main, 22, 44, Uninitialized, 22, 44, Point { x → 4, y → 5 }]
```

The method returns slot 6 -- a fresh `Point` with copied field values.
Displayed: `Point { flag: Owned, x: 22, y: 44 }`.

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
The interpreter resolves the receiver's class,
looks up the method, creates a new stack frame,
and evaluates the body:

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
copying the `Adder` out of its slot.
Then it looks up `sum` on class `Adder`,
creates a stack frame with `self` bound to the copied adder,
and evaluates the body.

## Access modes at runtime

The type checker verifies that access modes are used correctly.
The interpreter executes them:

| Access | Runtime behavior |
| --- | --- |
| `give` | Copy the value, mark the source uninitialized |
| `ref` | Copy with the object flag set to `Ref` |
| `mut` | Create a `Pointer` to the source slot |
| `share` | Copy with the object flag set to `Shared` |

### Ref produces a copy

A `ref` access creates an independent copy of the data,
tagged with the `Ref` flag.
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
    "Data { flag: Owned }"
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
