# Introduce Elaborator

## Motivation

We want to be able to do syntactic transformations to Dada source to introduce defaults.

As first step, we'll introduce an `elaborator` module with a newtype'd program term `ElaboratedProgram` and modify the type-checking env + interpreter to store it. This will ensure that elaboration has taken place.

For the moment, elaboration will be a no-op.

## Design Notes

### Mutation shape

`ElaboratedProgram::new(&Program)` clones the program into a local `Program`, runs a private free function `elaborate(&mut Program)` inside the `elaborator` module, then wraps the result in `Arc` and stores it in the struct. This avoids any `Arc::make_mut` dance: mutation happens before the `Arc` exists. The `elaborate` fn is module-private — callers only see `ElaboratedProgram::new`, which guarantees elaboration has run.

### Visibility inside the type checker

`Env` stores an `ElaboratedProgram` (not `Arc<Program>`). The existing `Env::program(&self) -> &Program` accessor continues to return a `&Program`, so the rest of the type checker is unchanged. `ElaboratedProgram` also implements `Deref<Target = Program>` for ergonomic access. Net effect: the newtype is enforced at construction and stored in `Env`, but largely invisible to callers.

### Interpreter

`Machine` stores an owned `ElaboratedProgram` (cloned — cheap, since it's just an `Arc<Program>` inside). The `'a` lifetime on `Machine` for the program reference goes away. Access via `Deref`/accessor as with `Env`.

### Test macros

All test macros in `src/test_util.rs` (`assert_ok!`, `assert_err!`, `assert_interpret!` and friends) route through `ElaboratedProgram::new`, so every test exercises elaboration (currently a no-op).

## Implementation checklist

- [x] Stub `src/elaborator.rs` with `ElaboratedProgram` newtype
- [x] Private free fn `elaborate(&mut Program)`, called from constructor before `Arc` wrap
- [x] `impl Deref<Target = Program> for ElaboratedProgram`
- [x] `Env` stores `ElaboratedProgram`; `Env::program()` still returns `&Program`
- [x] `type_system::check_program` (and `check_decl`, `check_class`) take `ElaboratedProgram`
- [x] `Interpreter` stores owned `ElaboratedProgram`; dropped `'a` lifetime
- [x] `src/lib.rs` entry point constructs `ElaboratedProgram::elaborate(&program)`
- [x] `src/test_util.rs` macros route through `ElaboratedProgram::elaborate`
- [x] `cargo test --all --workspace` green (629 passing)

## Gotchas encountered

- **`#[term]` generates a `::new` constructor that bypasses elaboration.** For a struct, `#[term]` auto-generates `ElaboratedProgram::new(program: impl Upcast<Arc<Program>>)`, which would let callers skip elaboration. To close that hole, `ElaboratedProgram` is **not** a `#[term]`. Instead it is a regular struct that hand-derives `Clone, Ord, Eq, PartialEq, PartialOrd, Hash`, hand-implements `Debug`, and uses `formality_core::cast_impl!` — the same pattern `Env` uses. This gives it everything needed to appear as a `judgment_fn!` parameter without gaining a bypass constructor. The elaborating constructor is `ElaboratedProgram::elaborate(&Program)`.
- **Borrow checker in the interpreter.** Previously `Interpreter` held `program: &'a Program`, so `self.program.class_named(...)` returned a `&ClassDecl` whose lifetime was tied to `'a`, not to `self`. With owned storage, the borrow is now on `self`, which conflicted with subsequent `&mut self` calls in `drop_value`. Fixed by cloning the `ClassDecl` via `.map(ClassDecl::clone)` at the one site that hit this.
