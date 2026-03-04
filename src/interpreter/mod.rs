use std::sync::Arc;

use formality_core::{set, Map, Upcast};

use crate::grammar::{
    ClassDecl, ClassDeclBoundData, FieldId, MethodDeclBoundData, MethodId, NamedTy, Parameter,
    Perm, Program, Ty, TypeName, ValueId, Var,
};

use crate::type_system::env::Env;
use crate::type_system::predicates::prove_is_copy;
use std::fmt::Write;

/// Result of evaluating a statement or expression.
enum Outcome {
    /// Normal result with a value.
    Value(TypedValue),
    /// Break out of the innermost loop.
    Break,
    /// Return from the current method with a value.
    Return(TypedValue),
}

#[cfg(test)]
mod tests;

// ANCHOR: Alloc
/// A flat array of words representing a value in memory.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Alloc {
    data: Vec<Word>,
}
// ANCHOR_END: Alloc

// ANCHOR: Word
/// A single word of memory.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Word {
    Int(i64),
    Flags(Flags),
    Pointer(Pointer),
    RefCount(i64),
    Capacity(usize),
    Uninitialized,
}
// ANCHOR_END: Word

// ANCHOR: Flags
/// Permission flag for unique objects.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Flags {
    Uninitialized,
    Given,
    Shared,
    Borrowed,
}
// ANCHOR_END: Flags

// ANCHOR: Pointer
/// Identifies a position within an allocation.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Pointer {
    index: usize,
    offset: usize,
}
// ANCHOR_END: Pointer

/// Whether a type's layout includes a flags word.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum HasFlags {
    Yes,
    No,
}

impl HasFlags {
    fn to_usize(self) -> usize {
        match self {
            HasFlags::Yes => 1,
            HasFlags::No => 0,
        }
    }
}

// ANCHOR: TypedValue
/// A pointer paired with the type needed to interpret the words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedValue {
    pointer: Pointer,
    ty: Ty,
}
// ANCHOR_END: TypedValue

// ANCHOR: StackFrame
pub struct StackFrame {
    env: Env,
    variables: Map<Var, Pointer>,
}
// ANCHOR_END: StackFrame

// ANCHOR: Interpreter
pub struct Interpreter<'a> {
    program: &'a Program,
    allocs: Vec<Alloc>,
    output: String,
}
// ANCHOR_END: Interpreter

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program) -> Self {
        Self {
            program,
            allocs: Vec::new(),
            output: String::new(),
        }
    }

    /// Create a minimal Env for layout/predicate queries on concrete types.
    /// The interpreter works with fully monomorphized types, so no local
    /// variables or assumptions are needed.
    fn base_env(&self) -> Env {
        Env::new(Arc::new(self.program.clone()))
    }

    // ---------------------------------------------------------------
    // Low-level allocation and word operations
    // ---------------------------------------------------------------

    /// Allocate a new `Alloc` and return a pointer to its start.
    fn alloc_raw(&mut self, alloc: Alloc) -> Pointer {
        let index = self.allocs.len();
        self.allocs.push(alloc);
        Pointer { index, offset: 0 }
    }

    /// Allocate a single integer word.
    fn alloc_int(&mut self, n: i64) -> Pointer {
        self.alloc_raw(Alloc {
            data: vec![Word::Int(n)],
        })
    }

    /// Allocate a zero-sized allocation (used for unit values).
    fn alloc_unit(&mut self) -> Pointer {
        self.alloc_raw(Alloc { data: vec![] })
    }

    /// Allocate a unit value and wrap it in a TypedValue.
    fn unit_value(&mut self) -> TypedValue {
        TypedValue {
            pointer: self.alloc_unit(),
            ty: Ty::unit(),
        }
    }

    /// Read one word at a pointer.
    fn read_word(&self, ptr: Pointer) -> Word {
        self.allocs[ptr.index].data[ptr.offset]
    }

    /// Assert that a typed value is an integer and return its value.
    fn expect_int(&self, tv: &TypedValue) -> anyhow::Result<i64> {
        anyhow::ensure!(
            tv.ty.strip_perm() == Ty::int(),
            "expected Int, got {:?}",
            tv.ty
        );
        match self.read_word(tv.pointer) {
            Word::Int(n) => Ok(n),
            other => anyhow::bail!("expected Int word, got {other:?}"),
        }
    }

    /// Write one word at a pointer.
    fn write_word(&mut self, ptr: Pointer, word: Word) {
        self.allocs[ptr.index].data[ptr.offset] = word;
    }

    /// Read `count` words starting at a pointer.
    fn read_words(&self, ptr: Pointer, count: usize) -> Vec<Word> {
        self.allocs[ptr.index].data[ptr.offset..ptr.offset + count].to_vec()
    }

    /// Write a slice of words starting at a pointer.
    fn write_words(&mut self, ptr: Pointer, words: &[Word]) {
        let start = ptr.offset;
        for (i, &word) in words.iter().enumerate() {
            self.allocs[ptr.index].data[start + i] = word;
        }
    }

    // ---------------------------------------------------------------
    // Type-driven helpers
    // ---------------------------------------------------------------

    /// Does this type have a flags word in its layout?
    /// A named class type has flags when it is not copy (i.e., move).
    /// This depends on the instantiated type, not just the class predicate —
    /// e.g. `shared class Box[ty T]` has no flags when T is copy (Box[Int])
    /// but has flags when T is move (Box[Data]).
    fn has_flags(&self, env: &Env, ty: &Ty) -> HasFlags {
        let inner = ty.strip_perm();
        match &inner {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(_),
                ..
            }) => {
                if self.is_copy_type(env, &inner) {
                    HasFlags::No
                } else {
                    HasFlags::Yes
                }
            }
            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                ..
            }) => HasFlags::Yes,
            Ty::NamedTy(NamedTy {
                name: TypeName::Int | TypeName::Tuple(_),
                ..
            }) => HasFlags::No,
            // After strip_perm, ApplyPerm is impossible.
            // Var is impossible in the interpreter (fully monomorphized).
            Ty::Var(_) | Ty::ApplyPerm(..) => {
                unreachable!("has_flags called on non-concrete type: {inner:?}")
            }
        }
    }

    /// Compute the word offset and type of a field within a class allocation.
    fn field_offset_by_name(
        &self,
        env: &Env,
        class_name: &ValueId,
        parameters: &[Parameter],
        field_id: &FieldId,
    ) -> anyhow::Result<(usize, Ty)> {
        let class_decl = self.program.class_named(class_name)?;
        let class_data = class_decl.binder.instantiate_with(parameters)?;
        let class_ty = Ty::NamedTy(NamedTy {
            name: class_name.upcast(),
            parameters: parameters.to_vec(),
        });
        let mut offset = self.has_flags(env, &class_ty).to_usize();
        for field in &class_data.fields {
            if field.name == *field_id {
                return Ok((offset, field.ty.clone()));
            }
            offset += self.size_of(env, &field.ty)?;
        }
        anyhow::bail!("no field `{field_id:?}` in class `{class_name:?}`")
    }

    /// Determine if a parameter (type or permission) is copy.
    fn is_copy_parameter(&self, env: &Env, param: &Parameter) -> anyhow::Result<bool> {
        Ok(prove_is_copy(env, param).is_proven())
    }

    /// Check if a type is copy (delegates to the type system).
    fn is_copy_type(&self, env: &Env, ty: &Ty) -> bool {
        self.is_copy_parameter(env, &Parameter::Ty(ty.clone()))
            .unwrap_or(false)
    }

    /// Compute the size (in Words) of a type.
    fn size_of(&self, env: &Env, ty: &Ty) -> anyhow::Result<usize> {
        match ty {
            Ty::ApplyPerm(_, inner) => self.size_of(env, inner),
            Ty::Var(v) => anyhow::bail!("size_of on non-monomorphized type variable `{v:?}`"),
            Ty::NamedTy(NamedTy { name, parameters }) => match name {
                TypeName::Int => Ok(1),
                TypeName::Array => Ok(2), // Word::Flags + Word::Pointer
                TypeName::Tuple(_) => {
                    let mut total = 0;
                    for param in parameters {
                        let Parameter::Ty(ty) = param else {
                            anyhow::bail!("tuple parameter is not a type: `{param:?}`");
                        };
                        total += self.size_of(env, ty)?;
                    }
                    Ok(total)
                }
                TypeName::Id(class_name) => {
                    let class_decl = self.program.class_named(class_name)?;

                    let ClassDeclBoundData {
                        predicates: _,
                        fields,
                        methods: _,
                    } = class_decl.binder.instantiate_with(parameters)?;

                    let mut total = self.has_flags(env, ty).to_usize();
                    for field in &fields {
                        total += self.size_of(env, &field.ty)?;
                    }

                    Ok(total)
                }
            },
        }
    }

    // ---------------------------------------------------------------
    // Core value operations
    // ---------------------------------------------------------------

    /// Copy N words (determined by type) into a new allocation.
    fn copy_value(&mut self, env: &Env, ptr: Pointer, ty: &Ty) -> anyhow::Result<TypedValue> {
        let size = self.size_of(env, ty)?;
        let words = self.read_words(ptr, size);
        let new_ptr = self.alloc_raw(Alloc { data: words });
        Ok(TypedValue {
            pointer: new_ptr,
            ty: ty.clone(),
        })
    }

    /// Copy a value and overwrite its flags.
    fn copy_with_flag(&mut self, env: &Env, ptr: Pointer, ty: &Ty, flag: Flags) -> anyhow::Result<TypedValue> {
        let tv = self.copy_value(env, ptr, ty)?;
        if self.has_flags(env, ty) == HasFlags::Yes {
            self.write_flags(env, tv.pointer, ty, flag)?;
        }
        Ok(tv)
    }

    /// Give a value: copy it out of `ptr` according to its flags.
    /// - Given: move (copy + uninitialize source)
    /// - Shared: copy + share_op (increment refcounts for the duplicate)
    /// - Borrowed: copy (no ownership transfer)
    /// - Uninitialized: fault
    /// - No flags (copy type): copy
    fn give_value(
        &mut self,
        env: &Env,
        ptr: Pointer,
        ty: &Ty,
        flags: Option<Flags>,
        op: &str,
    ) -> anyhow::Result<TypedValue> {
        match flags {
            Some(Flags::Given) => {
                let copied = self.copy_value(env, ptr, ty)?;
                self.uninitialize(env, ptr, ty)?;
                Ok(copied)
            }
            Some(Flags::Shared) => {
                let copied = self.copy_with_flag(env, ptr, ty, Flags::Shared)?;
                self.share_op(env, copied.pointer, ty)?;
                Ok(copied)
            }
            Some(Flags::Borrowed) => {
                Ok(self.copy_with_flag(env, ptr, ty, Flags::Borrowed)?)
            }
            Some(Flags::Uninitialized) => {
                anyhow::bail!("{op}: give of uninitialized value")
            }
            None => {
                Ok(self.copy_value(env, ptr, ty)?)
            }
        }
    }

    /// Mark a value as uninitialized.
    /// Sets the flags word to Flags::Uninitialized (if present) and
    /// overwrites all remaining data words with Word::Uninitialized.
    fn uninitialize(&mut self, env: &Env, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let flags_size = self.has_flags(env, ty).to_usize();
        if flags_size > 0 {
            self.write_word(ptr, Word::Flags(Flags::Uninitialized));
        }
        let size = self.size_of(env, ty)?;
        for i in flags_size..size {
            self.write_word(
                Pointer {
                    index: ptr.index,
                    offset: ptr.offset + i,
                },
                Word::Uninitialized,
            );
        }
        Ok(())
    }

    /// Read the flags of a value, if it has them.
    fn read_flags(&self, env: &Env, ptr: Pointer, ty: &Ty) -> anyhow::Result<Option<Flags>> {
        if self.has_flags(env, ty) == HasFlags::Yes {
            match self.read_word(ptr) {
                Word::Flags(f) => Ok(Some(f)),
                other => anyhow::bail!("expected Flags word, got {other:?}"),
            }
        } else {
            Ok(None)
        }
    }

    /// Write flags for a value.
    fn write_flags(&mut self, env: &Env, ptr: Pointer, ty: &Ty, flags: Flags) -> anyhow::Result<()> {
        anyhow::ensure!(
            self.has_flags(env, ty) == HasFlags::Yes,
            "write_flags on type without flags"
        );
        self.write_word(ptr, Word::Flags(flags));
        Ok(())
    }

    /// Compute effective flags for a value accessed through an outer context.
    /// When the outer context is Shared or Borrowed, that overrides the value's
    /// runtime flags (unless the value is uninitialized or has no flags).
    /// This is the uniform rule for: place traversal through field projections,
    /// array element access, and any future "access through a permission boundary."
    fn effective_flags(
        &self,
        env: &Env,
        outer: Flags,
        value_ptr: Pointer,
        value_ty: &Ty,
    ) -> anyhow::Result<Option<Flags>> {
        match outer {
            Flags::Given => self.read_flags(env, value_ptr, value_ty),
            Flags::Shared | Flags::Borrowed => {
                if self.has_flags(env, &value_ty.strip_perm()) == HasFlags::No {
                    Ok(None)
                } else {
                    let runtime = self.read_flags(env, value_ptr, value_ty)?;
                    if runtime == Some(Flags::Uninitialized) {
                        Ok(Some(Flags::Uninitialized))
                    } else {
                        Ok(Some(outer))
                    }
                }
            }
            Flags::Uninitialized => {
                anyhow::bail!("access through uninitialized value")
            }
        }
    }

    /// Extract the allocation pointer from an Array TypedValue.
    fn expect_array_ptr(&self, tv: &TypedValue) -> anyhow::Result<Pointer> {
        self.expect_array_ptr_from_value(tv.pointer)
    }

    /// Extract the allocation pointer from an Array value at the given pointer.
    /// The value is two words: [Flags, Pointer].
    fn expect_array_ptr_from_value(&self, ptr: Pointer) -> anyhow::Result<Pointer> {
        match self.read_word(ptr) {
            Word::Flags(Flags::Uninitialized) => anyhow::bail!("access of uninitialized array"),
            _ => {}
        }
        let ptr_word = self.read_word(Pointer {
            index: ptr.index,
            offset: ptr.offset + 1,
        });
        match ptr_word {
            Word::Pointer(alloc_ptr) => Ok(alloc_ptr),
            other => anyhow::bail!("expected Pointer word, got {other:?}"),
        }
    }

    /// Read the refcount from an array allocation (stored at offset 0).
    fn read_refcount(&self, array_alloc_ptr: Pointer) -> anyhow::Result<i64> {
        match self.read_word(array_alloc_ptr) {
            Word::RefCount(n) => Ok(n),
            other => anyhow::bail!("expected RefCount word, got {other:?}"),
        }
    }

    /// Write a new refcount to an array allocation (at offset 0).
    fn write_refcount(&mut self, array_alloc_ptr: Pointer, refcount: i64) {
        self.write_word(array_alloc_ptr, Word::RefCount(refcount));
    }

    /// Check that index is within array bounds.
    fn check_array_bounds(&self, array_ptr: Pointer, index: usize, op: &str) -> anyhow::Result<()> {
        let capacity = match self.read_word(Pointer {
            index: array_ptr.index,
            offset: 1,
        }) {
            Word::Capacity(n) => n,
            other => anyhow::bail!("{op}: expected Capacity word, got {other:?}"),
        };
        anyhow::ensure!(
            index < capacity,
            "{op}: index {index} out of bounds (capacity {capacity})"
        );
        Ok(())
    }

    /// Check that an array element is initialized. Faults if not.
    fn check_element_initialized(&self, elem_ptr: Pointer, op: &str) -> anyhow::Result<()> {
        match self.read_word(elem_ptr) {
            Word::Flags(Flags::Uninitialized) | Word::Uninitialized => {
                anyhow::bail!("{op}: element is uninitialized")
            }
            _ => Ok(()),
        }
    }

    /// Check that an array element slot is uninitialized (for initialization).
    fn check_element_uninitialized(&self, elem_ptr: Pointer, op: &str) -> anyhow::Result<()> {
        match self.read_word(elem_ptr) {
            Word::Flags(Flags::Uninitialized) | Word::Uninitialized => Ok(()),
            _ => anyhow::bail!("{op}: element is already initialized"),
        }
    }

    /// Convert a value from Given to Shared ownership in place.
    /// Called by Expr::Share. Flips only the outermost flags word.
    /// Inner fields keep their runtime flags — the type system
    /// (via resolve_place) enforces shared semantics on traversal.
    fn convert_to_shared(&mut self, env: &Env, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let inner_ty = ty.strip_perm();
        if self.has_flags(env, &inner_ty) == HasFlags::Yes {
            if let Word::Flags(Flags::Given) = self.read_word(ptr) {
                self.write_word(ptr, Word::Flags(Flags::Shared));
            }
        }
        Ok(())
    }

    /// Duplication accounting: called when a Shared value is copied
    /// (by place.give or place.ref on Shared). Increments array refcounts
    /// and recurses into class fields to account for nested duplications.
    fn share_op(&mut self, env: &Env, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let inner_ty = ty.strip_perm();
        match &inner_ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name)?;
                let class_data = class_decl.binder.instantiate_with(parameters)?;
                let mut offset = self.has_flags(env, &inner_ty).to_usize();
                for field in &class_data.fields {
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    self.share_op(env, field_ptr, &field.ty)?;
                    offset += self.size_of(env, &field.ty)?;
                }
                Ok(())
            }
            // Array: increment the ref count of the underlying allocation.
            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                ..
            }) => {
                let array_alloc_ptr = self.expect_array_ptr_from_value(ptr)?;
                let refcount = self.read_refcount(array_alloc_ptr)?;
                self.write_refcount(array_alloc_ptr, refcount + 1);
                Ok(())
            }
            // Int, Tuple: no refcounted resources to duplicate.
            Ty::NamedTy(NamedTy {
                name: TypeName::Int | TypeName::Tuple(_),
                ..
            }) => Ok(()),
            Ty::Var(_) | Ty::ApplyPerm(..) => {
                unreachable!("share_op called on non-concrete type: {inner_ty:?}")
            }
        }
    }

    /// Drop an owned value (Given or Shared): recursively drop owned fields,
    /// then uninitialize. Given and Shared converge at every leaf — a Given
    /// array with refcount 1 decrements the same way as a Shared array.
    fn drop_owned_value(&mut self, env: &Env, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let inner_ty = ty.strip_perm();
        match &inner_ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name)?;
                let class_data = class_decl.binder.instantiate_with(parameters)?;
                let mut offset = self.has_flags(env, &inner_ty).to_usize();
                for field in &class_data.fields {
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    // Recursively drop fields that are owned (Given or Shared)
                    if let Some(field_flags) = self.read_flags(env, field_ptr, &field.ty)? {
                        match field_flags {
                            Flags::Given | Flags::Shared => {
                                self.drop_owned_value(env, field_ptr, &field.ty)?;
                            }
                            Flags::Borrowed | Flags::Uninitialized => {}
                        }
                    }
                    offset += self.size_of(env, &field.ty)?;
                }
                // Uninitialize this value
                self.uninitialize(env, ptr, &inner_ty)?;
                Ok(())
            }
            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                parameters,
            }) => {
                self.drop_array(env, ptr, parameters, &inner_ty)?;
                Ok(())
            }
            // Int, Tuple: just uninitialize (no recursive structure).
            Ty::NamedTy(NamedTy {
                name: TypeName::Int | TypeName::Tuple(_),
                ..
            }) => {
                self.uninitialize(env, ptr, &inner_ty)?;
                Ok(())
            }
            Ty::Var(_) | Ty::ApplyPerm(..) => {
                unreachable!("drop_owned_value called on non-concrete type: {inner_ty:?}")
            }
        }
    }

    /// Drop an array reference: decrement refcount, and if it reaches zero,
    /// recursively drop all initialized elements and free the allocation.
    /// Then uninitialize the value (the two-word [Flags, Pointer] representation).
    fn drop_array(
        &mut self,
        env: &Env,
        ptr: Pointer,
        parameters: &[Parameter],
        inner_ty: &Ty,
    ) -> anyhow::Result<()> {
        let element_ty = extract_array_element_ty(parameters)?;
        let array_alloc_ptr = self.expect_array_ptr_from_value(ptr)?;
        let refcount = self.read_refcount(array_alloc_ptr)?;
        anyhow::ensure!(refcount > 0, "drop_array: refcount already zero");
        let new_refcount = refcount - 1;
        self.write_refcount(array_alloc_ptr, new_refcount);

        if new_refcount == 0 {
            // Refcount reached zero: drop all initialized elements, then free.
            let capacity = match self.read_word(Pointer {
                index: array_alloc_ptr.index,
                offset: 1,
            }) {
                Word::Capacity(n) => n,
                other => anyhow::bail!("drop_array: expected Capacity word, got {other:?}"),
            };
            let element_size = self.size_of(env, &element_ty)?;
            for i in 0..capacity {
                let elem_ptr = Pointer {
                    index: array_alloc_ptr.index,
                    offset: 2 + i * element_size,
                };
                // Dispatch drop based on element flags (skip uninitialized)
                if let Some(flags) = self.read_flags(env, elem_ptr, &element_ty)? {
                    match flags {
                        Flags::Given | Flags::Shared => {
                            self.drop_owned_value(env, elem_ptr, &element_ty)?;
                        }
                        Flags::Borrowed | Flags::Uninitialized => {}
                    }
                } else {
                    // Non-flagged element (e.g., Int): check if initialized
                    match self.read_word(elem_ptr) {
                        Word::Uninitialized => {} // skip
                        _ => {}                   // Int etc: nothing to drop
                    }
                }
            }
            // Free the backing allocation by overwriting all words with Uninitialized
            let alloc_len = self.allocs[array_alloc_ptr.index].data.len();
            for i in 0..alloc_len {
                self.allocs[array_alloc_ptr.index].data[i] = Word::Uninitialized;
            }
        }

        // Uninitialize the value representation (the [Flags, Pointer] words)
        self.uninitialize(env, ptr, inner_ty)?;
        Ok(())
    }

    /// Free a TypedValue: drop its content, then overwrite ALL words with
    /// Word::Uninitialized. The allocation becomes dead memory — any subsequent
    /// access is a fault.
    ///
    /// This is the uniform cleanup operation for temporaries: every expression
    /// evaluation yields a fresh allocation, and consumers en done.
    fn free(&mut self, env: &Env, tv: &TypedValue) -> anyhow::Result<()> {
        // Step 1: Drop content (recurse into flagged fields, decrement refcounts)
        if let Some(flags) = self.read_flags(env, tv.pointer, &tv.ty)? {
            match flags {
                Flags::Given | Flags::Shared => {
                    self.drop_owned_value(env, tv.pointer, &tv.ty)?;
                }
                Flags::Borrowed | Flags::Uninitialized => {}
            }
        }
        // Step 2: Overwrite ALL words with Uninitialized (including flags)
        let size = self.size_of(env, &tv.ty.strip_perm())?;
        for i in 0..size {
            self.write_word(
                Pointer {
                    index: tv.pointer.index,
                    offset: tv.pointer.offset + i,
                },
                Word::Uninitialized,
            );
        }
        Ok(())
    }

    /// Resolve a grammar Place to a pointer.
    ///
    /// Walks the allocation layout to compute the byte offset for the place.
    /// Callers that need the type should use `env.place_ty(place)` separately.
    fn resolve_place(
        &self,
        stack_frame: &StackFrame,
        place: &crate::grammar::Place,
    ) -> anyhow::Result<(Pointer, Flags)> {
        let var_ptr = stack_frame
            .variables
            .get(&place.var)
            .ok_or_else(|| anyhow::anyhow!("undefined variable `{:?}`", place.var))?;

        let env = &stack_frame.env;

        // Walk projections to compute the pointer offset.
        // At each step, build the prefix place and ask env.place_ty for
        // the type — this is the single source of truth for permissions.
        //
        // Track effective flags: accumulates the "last non-affine permission"
        // seen while traversing. Given/mut are identity (don't change it);
        // ref/shared take over. This makes sharing shallow — inner fields
        // keep their runtime Given flags, but the effective permission
        // reflects the path we traversed.
        let mut current_ptr = *var_ptr;
        let mut effective = Flags::Given;
        let mut prefix_place = crate::grammar::Place {
            var: place.var.clone(),
            projections: vec![],
        };

        for projection in &place.projections {
            match projection {
                crate::grammar::Projection::Field(field_id) => {
                    let prefix_ty = env.place_ty(&prefix_place)?;

                    // Check flags before projecting through a class value.
                    // Per the spec, accessing through an Uninitialized value is UB.
                    if let Some(Flags::Uninitialized) = self.read_flags(env, current_ptr, &prefix_ty)? {
                        anyhow::bail!(
                            "access through uninitialized value: `{:?}.{:?}`",
                            place.var,
                            field_id
                        );
                    }

                    // Update effective flags: non-affine permissions take over.
                    if let Ty::ApplyPerm(perm, _) = &prefix_ty {
                        match perm {
                            Perm::Rf(_) => effective = Flags::Borrowed,
                            Perm::Shared => effective = Flags::Shared,
                            // Given, Mv, Mt: affine permissions, identity
                            Perm::Given | Perm::Mv(_) | Perm::Mt(_) => {}
                            Perm::Var(_) | Perm::Apply(..) => {}
                        }
                    }

                    let inner_ty = prefix_ty.strip_perm();
                    match &inner_ty {
                        Ty::NamedTy(NamedTy {
                            name: TypeName::Id(class_name),
                            parameters,
                        }) => {
                            let (field_offset, _field_ty) =
                                self.field_offset_by_name(env, class_name, parameters, field_id)?;
                            current_ptr = Pointer {
                                index: current_ptr.index,
                                offset: current_ptr.offset + field_offset,
                            };
                        }
                        _ => anyhow::bail!("field access on non-class type: {prefix_ty:?}"),
                    }

                    prefix_place = prefix_place.project(projection.clone());
                }
            }
        }

        Ok((current_ptr, effective))
    }

    // ---------------------------------------------------------------
    // Display
    // ---------------------------------------------------------------

    pub fn output(&self) -> &str {
        &self.output
    }

    /// Dump live (non-freed) allocations, one line per alloc.
    /// Uses zero-padded hex indices for visual alignment.
    /// An allocation is "freed" if it is empty or all words are Uninitialized.
    pub fn dump_heap(&self) -> Vec<String> {
        let max_index = self.allocs.len();
        // Compute hex digit width: at least 2 digits, enough for all indices
        let hex_width = if max_index <= 0x100 { 2 } else { 3 };
        self.allocs
            .iter()
            .enumerate()
            .filter(|(_, alloc)| {
                !alloc.data.is_empty()
                    && !alloc.data.iter().all(|w| {
                        matches!(w, Word::Uninitialized | Word::Flags(Flags::Uninitialized))
                    })
            })
            .map(|(i, alloc)| {
                let words: Vec<String> =
                    alloc.data.iter().map(|w| fmt_word(w, hex_width)).collect();
                format!("0x{i:0>width$x}: [{}]", words.join(", "), width = hex_width)
            })
            .collect()
    }

    /// Pretty-print a typed value for display.
    pub fn display_value(&self, env: &Env, tv: &TypedValue) -> String {
        let mut buf = String::new();
        self.fmt_value(env, &mut buf, tv.pointer, &tv.ty);
        buf
    }

    fn fmt_value(&self, env: &Env, buf: &mut String, ptr: Pointer, ty: &Ty) {
        // Show permission prefix when the type has an ApplyPerm wrapper.
        // Uses Debug formatting which follows the grammar annotations,
        // e.g. `ref [place1, place2]`, `shared`, `given`.
        if let Ty::ApplyPerm(perm, _) = ty {
            write!(buf, "{perm:?} ").unwrap();
        }
        let inner_ty = ty.strip_perm();
        match &inner_ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Int,
                ..
            }) => match self.read_word(ptr) {
                Word::Int(n) => write!(buf, "{n}").unwrap(),
                Word::Uninitialized => write!(buf, "uninitialized").unwrap(),
                other => write!(buf, "<unexpected: {other:?}>").unwrap(),
            },

            Ty::NamedTy(NamedTy {
                name: TypeName::Tuple(0),
                ..
            }) => {
                // Unit: zero words, nothing to display
                write!(buf, "()").unwrap();
            }

            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name).unwrap();
                let class_data = class_decl.binder.instantiate_with(parameters).unwrap();
                let has_flags = self.has_flags(env, &inner_ty) == HasFlags::Yes;

                write!(buf, "{class_name:?}").unwrap();
                write!(buf, " {{ ").unwrap();

                let mut first = true;

                if has_flags {
                    let flags_word = self.read_word(ptr);
                    match flags_word {
                        Word::Flags(f) => write!(buf, "flag: {f:?}").unwrap(),
                        _ => write!(buf, "flag: <invalid>").unwrap(),
                    }
                    first = false;
                }

                let mut offset = if has_flags { 1 } else { 0 };
                for field in &class_data.fields {
                    if !first {
                        write!(buf, ", ").unwrap();
                    }
                    first = false;
                    write!(buf, "{:?}: ", field.name).unwrap();
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    self.fmt_value(env, buf, field_ptr, &field.ty);
                    offset += self.size_of(env, &field.ty).unwrap();
                }

                write!(buf, " }}").unwrap();
            }

            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                parameters,
            }) => {
                let element_ty = extract_array_element_ty(parameters).unwrap();
                let flags = match self.read_word(ptr) {
                    Word::Flags(f) => f,
                    other => {
                        write!(buf, "<unexpected: {other:?}>").unwrap();
                        return;
                    }
                };
                if flags == Flags::Uninitialized {
                    write!(buf, "uninitialized").unwrap();
                    return;
                }
                let array_ptr = match self.read_word(Pointer {
                    index: ptr.index,
                    offset: ptr.offset + 1,
                }) {
                    Word::Pointer(p) => p,
                    other => {
                        write!(buf, "<unexpected pointer: {other:?}>").unwrap();
                        return;
                    }
                };
                write!(buf, "Array {{ flag: {flags:?}").unwrap();
                let refcount = self.read_refcount(array_ptr).unwrap_or(-1);
                write!(buf, ", rc: {refcount}").unwrap();
                let Word::Capacity(capacity) = self.read_word(Pointer {
                    index: array_ptr.index,
                    offset: 1,
                }) else {
                    write!(buf, ", <bad capacity> }}").unwrap();
                    return;
                };
                let element_size = self.size_of(env, &element_ty).unwrap();
                for i in 0..capacity as usize {
                    write!(buf, ", ").unwrap();
                    let elem_ptr = Pointer {
                        index: array_ptr.index,
                        offset: 2 + i * element_size,
                    };
                    self.fmt_value(env, buf, elem_ptr, &element_ty);
                }
                write!(buf, " }}").unwrap();
            }

            Ty::NamedTy(NamedTy {
                name: TypeName::Tuple(_),
                ..
            }) => {
                // Non-unit tuples: display raw word representation
                write!(buf, "<tuple>").unwrap();
            }
            Ty::Var(_) | Ty::ApplyPerm(..) => {
                unreachable!("fmt_value called on non-concrete type: {inner_ty:?}")
            }
        }
    }

    // ---------------------------------------------------------------
    // Instantiation
    // ---------------------------------------------------------------

    fn instantiate_class(
        &mut self,
        env: &Env,
        class_name: &ValueId,
        parameters: &[Parameter],
        field_values: &[TypedValue],
    ) -> anyhow::Result<TypedValue> {
        let class_decl = self.program.class_named(class_name)?;

        let ClassDeclBoundData {
            predicates: _,
            fields,
            methods: _,
        } = class_decl.binder.instantiate_with(parameters)?;

        if fields.len() != field_values.len() {
            anyhow::bail!(
                "class `{class_name:?}` has {} fields but {} were provided",
                fields.len(),
                field_values.len()
            );
        }

        // Build flat allocation
        let mut data = Vec::new();

        // Flags word for non-copy class instantiations
        let class_ty = Ty::NamedTy(NamedTy {
            name: class_name.upcast(),
            parameters: parameters.to_vec(),
        });
        let has_flags = self.has_flags(env, &class_ty) == HasFlags::Yes;
        if has_flags {
            data.push(Word::Flags(Flags::Given));
        }

        // Copy field words into the allocation
        for (field_decl, field_tv) in fields.iter().zip(field_values) {
            let field_size = self.size_of(env, &field_decl.ty)?;
            let words = self.read_words(field_tv.pointer, field_size);
            data.extend_from_slice(&words);
        }

        let ptr = self.alloc_raw(Alloc { data });
        let ty = Ty::NamedTy(NamedTy {
            name: class_name.upcast(),
            parameters: parameters.to_vec(),
        });
        Ok(TypedValue { pointer: ptr, ty })
    }

    // ---------------------------------------------------------------
    // Method finding and calling
    // ---------------------------------------------------------------

    fn find_method(
        &self,
        class_name: &ValueId,
        class_parameters: &[Parameter],
        method_id: &MethodId,
        method_parameters: &[Parameter],
    ) -> anyhow::Result<MethodDeclBoundData> {
        let ClassDecl {
            name: _,
            class_predicate: _,
            binder,
        } = self.program.class_named(class_name)?;

        let ClassDeclBoundData {
            predicates: _,
            fields: _,
            methods,
        } = binder.instantiate_with(class_parameters)?;

        let method_decl = methods
            .iter()
            .find(|m| m.name == *method_id)
            .ok_or_else(|| {
                anyhow::anyhow!("class `{class_name:?}` has no method `{method_id:?}`")
            })?;

        let method_data = method_decl.binder.instantiate_with(method_parameters)?;
        Ok(method_data)
    }

    fn call_method(
        &mut self,
        class_name: &ValueId,
        class_parameters: &[Parameter],
        method_id: &MethodId,
        method_parameters: &[Parameter],
        this: TypedValue,
        input_values: Vec<TypedValue>,
    ) -> anyhow::Result<TypedValue> {
        let MethodDeclBoundData {
            this: this_decl,
            inputs,
            output: _,
            predicates: _,
            body,
        } = self.find_method(class_name, class_parameters, method_id, method_parameters)?;

        if inputs.len() != input_values.len() {
            anyhow::bail!(
                "method `{method_id:?}` of class `{class_name:?}` has {} parameters but {} were provided",
                inputs.len(),
                input_values.len()
            );
        }

        // Build a fresh env and stack frame for the new method.
        let mut env = self.base_env();

        // Compute `this` type: apply the method's declared permission to the class type.
        // (Given is the identity permission — don't wrap.)
        let this_ty = match &this_decl.perm {
            Perm::Given => this.ty,
            perm => Ty::apply_perm(perm, this.ty),
        };
        env = env.push_local_variable(Var::This, this_ty)?;

        let mut stack_frame = StackFrame {
            env,
            variables: Default::default(),
        };
        stack_frame.variables.insert(Var::This, this.pointer);
        for (input, input_value) in inputs.iter().zip(input_values) {
            let var = Var::Id(input.name.clone());
            stack_frame.env = stack_frame.env.push_local_variable(var.clone(), input_value.ty)?;
            stack_frame.variables.insert(var, input_value.pointer);
        }

        match &body {
            crate::grammar::MethodBody::Trusted => anyhow::bail!(
                "method `{method_id:?}` of class `{class_name:?}` is trusted and cannot be called by the interpreter",
            ),
            crate::grammar::MethodBody::Block(block) => {
                let result_tv = match self.eval_block(&mut stack_frame, block)? {
                    Outcome::Value(tv) => tv,
                    Outcome::Return(tv) => tv,
                    Outcome::Break => anyhow::bail!("break outside of loop"),
                };
                // Free any variables remaining in the stack frame (end-of-scope cleanup).
                // The return value is a fresh allocation not in the frame, so this is safe.
                let env = &stack_frame.env;
                for (var, ptr) in &stack_frame.variables {
                    let ty = env.var_ty(var)?.clone();
                    let tv = TypedValue { pointer: *ptr, ty };
                    self.free(env, &tv)?;
                }
                Ok(result_tv)
            }
        }
    }

    // ---------------------------------------------------------------
    // Evaluation
    // ---------------------------------------------------------------

    /// Run a program by instantiating `Main()` and calling `main`.
    pub fn interpret(&mut self) -> anyhow::Result<TypedValue> {
        let main_class: ValueId = crate::dada_lang::try_term("Main")?;
        let main_method: MethodId = crate::dada_lang::try_term("main")?;
        let env = self.base_env();
        let object = self.instantiate_class(&env, &main_class, &[], &[])?;
        self.call_method(&main_class, &[], &main_method, &[], object, vec![])
    }

    fn eval_block(
        &mut self,
        stack_frame: &mut StackFrame,
        block: &crate::grammar::Block,
    ) -> anyhow::Result<Outcome> {
        let crate::grammar::Block { statements } = block;

        let mut final_value = self.unit_value();
        for statement in statements {
            match self.eval_statement(stack_frame, statement)? {
                Outcome::Value(tv) => {
                    self.free(&stack_frame.env, &final_value)?;
                    final_value = tv;
                }
                early @ (Outcome::Break | Outcome::Return(_)) => {
                    self.free(&stack_frame.env, &final_value)?;
                    return Ok(early);
                }
            }
        }
        Ok(Outcome::Value(final_value))
    }

    fn eval_statement(
        &mut self,
        stack_frame: &mut StackFrame,
        statement: &crate::grammar::Statement,
    ) -> anyhow::Result<Outcome> {
        match statement {
            crate::grammar::Statement::Expr(expr) => self.eval_expr(stack_frame, expr),

            crate::grammar::Statement::Let(name, _ascription, expr) => {
                let tv = self.eval_expr_value(stack_frame, expr)?;
                let var = Var::Id(name.clone());
                stack_frame.env = stack_frame.env.push_local_variable(var.clone(), tv.ty)?;
                stack_frame.variables.insert(var, tv.pointer);
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Statement::Reassign(place, expr) => {
                let tv = self.eval_expr_value(stack_frame, expr)?;
                let (target_ptr, _place_flags) = self.resolve_place(stack_frame, place)?;
                let target_ty = stack_frame.env.place_ty(place)?;
                // Drop the old value at the target before overwriting it.
                let old_tv = TypedValue {
                    pointer: target_ptr,
                    ty: target_ty.clone(),
                };
                let env = &stack_frame.env;
                self.free(env, &old_tv)?;
                // Bitwise copy: ownership moves into the target.
                let size = self.size_of(env, &target_ty)?;
                let words = self.read_words(tv.pointer, size);
                self.write_words(target_ptr, &words);
                // Scrub the temp without dropping — ownership was transferred.
                self.uninitialize(env, tv.pointer, &tv.ty)?;
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Statement::Loop(body) => loop {
                match self.eval_expr(stack_frame, body)? {
                    Outcome::Value(tv) => {
                        self.free(&stack_frame.env, &tv)?;
                    }
                    Outcome::Break => {
                        break Ok(Outcome::Value(self.unit_value()));
                    }
                    Outcome::Return(tv) => break Ok(Outcome::Return(tv)),
                }
            },

            crate::grammar::Statement::Break => Ok(Outcome::Break),

            crate::grammar::Statement::Return(expr) => {
                let tv = self.eval_expr_value(stack_frame, expr)?;
                Ok(Outcome::Return(tv))
            }

            crate::grammar::Statement::Print(expr) => {
                let tv = self.eval_expr_value(stack_frame, expr)?;
                let text = self.display_value(&stack_frame.env, &tv);
                self.free(&stack_frame.env, &tv)?;
                self.output.push_str(&text);
                self.output.push('\n');
                Ok(Outcome::Value(self.unit_value()))
            }
        }
    }

    fn eval_expr(
        &mut self,
        stack_frame: &mut StackFrame,
        expr: &crate::grammar::Expr,
    ) -> anyhow::Result<Outcome> {
        match expr {
            crate::grammar::Expr::Integer(n) => Ok(Outcome::Value(TypedValue {
                pointer: self.alloc_int(*n as i64),
                ty: Ty::int(),
            })),

            crate::grammar::Expr::Add(lhs, rhs) => {
                let l = self.eval_expr_value(stack_frame, lhs)?;
                let r = self.eval_expr_value(stack_frame, rhs)?;
                let a = self.expect_int(&l)?;
                let b = self.expect_int(&r)?;
                let env = &stack_frame.env;
                self.free(env, &l)?;
                self.free(env, &r)?;
                Ok(Outcome::Value(TypedValue {
                    pointer: self.alloc_int(a + b),
                    ty: Ty::int(),
                }))
            }

            crate::grammar::Expr::Block(block) => self.eval_block(stack_frame, block),

            crate::grammar::Expr::Tuple(exprs) => {
                for expr in exprs {
                    let tv = self.eval_expr_value(stack_frame, expr)?;
                    self.free(&stack_frame.env, &tv)?;
                }
                Ok(Outcome::Value(TypedValue {
                    pointer: self.alloc_raw(Alloc { data: vec![] }),
                    ty: Ty::unit(),
                }))
            }

            crate::grammar::Expr::New(class_name, params, field_exprs) => {
                let field_values: Vec<TypedValue> = field_exprs
                    .iter()
                    .map(|e| self.eval_expr_value(stack_frame, e))
                    .collect::<Result<_, _>>()?;
                let env = &stack_frame.env;
                let result = self.instantiate_class(
                    env,
                    class_name,
                    params,
                    &field_values,
                )?;
                for fv in &field_values {
                    // Scrub the temp without dropping — ownership moved into the class.
                    self.uninitialize(env, fv.pointer, &fv.ty)?;
                }
                Ok(Outcome::Value(result))
            }

            crate::grammar::Expr::Place(crate::grammar::PlaceExpr { place, access }) => {
                let (ptr, place_flags) = self.resolve_place(stack_frame, place)?;
                let place_ty = stack_frame.env.place_ty(place)?;
                let env = &stack_frame.env;
                let flags = self.effective_flags(env, place_flags, ptr, &place_ty)?;
                let tv = match access {
                    crate::grammar::Access::Gv => {
                        self.give_value(env, ptr, &place_ty, flags, "place.give")?
                    }
                    crate::grammar::Access::Rf => {
                        // Ref: result type = ref[place] applied to stripped place type.
                        let ref_perm = Perm::rf(set![place.clone()]);
                        let result_ty = Ty::apply_perm(ref_perm, place_ty.strip_perm());
                        match flags {
                            Some(Flags::Shared) => {
                                let copied = self.copy_with_flag(env, ptr, &place_ty, Flags::Shared)?;
                                self.share_op(env, copied.pointer, &place_ty)?;
                                TypedValue { pointer: copied.pointer, ty: result_ty }
                            }
                            Some(Flags::Given) | Some(Flags::Borrowed) => {
                                let copied = self.copy_with_flag(env, ptr, &place_ty, Flags::Borrowed)?;
                                TypedValue { pointer: copied.pointer, ty: result_ty }
                            }
                            Some(Flags::Uninitialized) => {
                                anyhow::bail!("ref of uninitialized value")
                            }
                            None => {
                                let copied = self.copy_value(env, ptr, &place_ty)?;
                                TypedValue { pointer: copied.pointer, ty: result_ty }
                            }
                        }
                    }
                    crate::grammar::Access::Mt => {
                        anyhow::bail!("mut access not yet implemented")
                    }
                    crate::grammar::Access::Drop => {
                        match flags {
                            Some(Flags::Given) | Some(Flags::Shared) => {
                                self.drop_owned_value(env, ptr, &place_ty)?;
                            }
                            Some(Flags::Borrowed) => {
                                // Borrowed: no-op
                            }
                            Some(Flags::Uninitialized) => {
                                anyhow::bail!("drop of uninitialized value")
                            }
                            None => {
                                // No flags (copy type): no-op
                            }
                        }
                        self.unit_value()
                    }
                };
                Ok(Outcome::Value(tv))
            }

            crate::grammar::Expr::Share(expr) => {
                let tv = self.eval_expr_value(stack_frame, expr)?;
                let env = &stack_frame.env;
                let flags = self.read_flags(env, tv.pointer, &tv.ty)?;
                match flags {
                    Some(Flags::Given) => {
                        self.convert_to_shared(env, tv.pointer, &tv.ty)?;
                    }
                    Some(Flags::Shared) | Some(Flags::Borrowed) => {
                        // Already shared or borrowed: no-op
                    }
                    Some(Flags::Uninitialized) => {
                        anyhow::bail!("share of uninitialized value")
                    }
                    None => {
                        // Copy type: no-op
                    }
                }
                // Share wraps the type with Perm::Shared.
                let result_ty = Ty::apply_perm(Perm::Shared, tv.ty.strip_perm());
                Ok(Outcome::Value(TypedValue { pointer: tv.pointer, ty: result_ty }))
            }

            crate::grammar::Expr::Call(receiver, method_name, method_params, args) => {
                let receiver_tv = self.eval_expr_value(stack_frame, receiver)?;
                let inner_ty = receiver_tv.ty.strip_perm();
                let (class_name, class_parameters) = match &inner_ty {
                    Ty::NamedTy(NamedTy {
                        name: TypeName::Id(id),
                        parameters,
                    }) => (id.clone(), parameters.clone()),
                    _ => anyhow::bail!("cannot call method on non-class type: {inner_ty:?}"),
                };
                let arg_vals: Vec<TypedValue> = args
                    .iter()
                    .map(|a| self.eval_expr_value(stack_frame, a))
                    .collect::<Result<_, _>>()?;
                Ok(Outcome::Value(self.call_method(
                    &class_name,
                    &class_parameters,
                    method_name,
                    method_params,
                    receiver_tv,
                    arg_vals,
                )?))
            }

            crate::grammar::Expr::If(cond, if_true, if_false) => {
                let cond_tv = self.eval_expr_value(stack_frame, cond)?;
                let n = self.expect_int(&cond_tv)?;
                self.free(&stack_frame.env, &cond_tv)?;
                if n != 0 {
                    self.eval_expr(stack_frame, if_true)
                } else {
                    self.eval_expr(stack_frame, if_false)
                }
            }

            crate::grammar::Expr::SizeOf(parameters) => {
                let ty = extract_size_of_ty(parameters)?;
                let size = self.size_of(&stack_frame.env, &ty)?;
                Ok(Outcome::Value(TypedValue {
                    pointer: self.alloc_int(size as i64),
                    ty: Ty::int(),
                }))
            }

            // ---------------------------------------------------------------
            // Array operations
            // ---------------------------------------------------------------
            crate::grammar::Expr::ArrayNew(parameters, length_expr) => {
                let (array_ty, element_ty) = extract_array_ty(parameters)?;
                let length_tv = self.eval_expr_value(stack_frame, length_expr)?;
                let length = self.expect_int(&length_tv)?;
                self.free(&stack_frame.env, &length_tv)?;
                anyhow::ensure!(length >= 0, "array_new: negative length {length}");
                let length = length as usize;
                let env = &stack_frame.env;
                let element_size = self.size_of(env, &element_ty)?;

                // Allocate: [Int(refcount), Int(length), element_slots...]
                // Each element slot has Flags::Uninitialized if the element type has flags,
                // otherwise Word::Uninitialized for all words.
                let has_flags = self.has_flags(env, &element_ty) == HasFlags::Yes;
                let mut data = vec![Word::RefCount(1), Word::Capacity(length)];
                for _ in 0..length {
                    if has_flags {
                        data.push(Word::Flags(Flags::Uninitialized));
                        data.extend(std::iter::repeat(Word::Uninitialized).take(element_size - 1));
                    } else {
                        data.extend(std::iter::repeat(Word::Uninitialized).take(element_size));
                    }
                }
                let alloc_ptr = self.alloc_raw(Alloc { data });

                // Two-word value: Flags + Pointer (same layout as non-copy classes)
                let value_ptr = self.alloc_raw(Alloc {
                    data: vec![Word::Flags(Flags::Given), Word::Pointer(alloc_ptr)],
                });
                Ok(Outcome::Value(TypedValue {
                    pointer: value_ptr,
                    ty: array_ty,
                }))
            }

            crate::grammar::Expr::ArrayCapacity(parameters, array_expr) => {
                let (_array_ty, _element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let capacity = self.read_word(Pointer {
                    index: array_ptr.index,
                    offset: 1,
                });
                self.free(&stack_frame.env, &array_tv)?;
                match capacity {
                    Word::Capacity(n) => Ok(Outcome::Value(TypedValue {
                        pointer: self.alloc_int(n as i64),
                        ty: Ty::int(),
                    })),
                    other => {
                        anyhow::bail!("array_capacity: expected Capacity word, got {other:?}")
                    }
                }
            }

            crate::grammar::Expr::ArrayGive(parameters, array_expr, index_expr) => {
                let (_array_ty, element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.expect_int(&index_tv)? as usize;
                let env = &stack_frame.env;
                self.free(env, &index_tv)?;
                let element_size = self.size_of(env, &element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_give")?;

                let elem_ptr = Pointer {
                    index: array_ptr.index,
                    offset: 2 + index * element_size,
                };

                // Check if element is uninitialized
                self.check_element_initialized(elem_ptr, "array_give")?;

                // Propagate the array's flags to element access: a shared array's
                // elements are accessed with shared semantics (copy + share_op),
                // even though the runtime flags on the element may be Given.
                let array_flags = match self.read_flags(env, array_tv.pointer, &array_tv.ty)? {
                    Some(f) => f,
                    None => Flags::Given,
                };
                let flags = self.effective_flags(env, array_flags, elem_ptr, &element_ty)?;
                let result = self.give_value(env, elem_ptr, &element_ty, flags, "array_give")?;

                self.free(env, &array_tv)?;
                Ok(Outcome::Value(result))
            }

            crate::grammar::Expr::ArrayDrop(parameters, array_expr, index_expr) => {
                let (_array_ty, element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.expect_int(&index_tv)? as usize;
                let env = &stack_frame.env;
                self.free(env, &index_tv)?;
                let element_size = self.size_of(env, &element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_drop")?;

                let elem_ptr = Pointer {
                    index: array_ptr.index,
                    offset: 2 + index * element_size,
                };

                // Check if element is uninitialized — dropping uninitialized is UB
                self.check_element_initialized(elem_ptr, "array_drop")?;

                // Propagate the array's flags to element drop, same as ArrayGive.
                let array_flags = match self.read_flags(env, array_tv.pointer, &array_tv.ty)? {
                    Some(f) => f,
                    None => Flags::Given,
                };
                if let Some(flags) = self.effective_flags(env, array_flags, elem_ptr, &element_ty)? {
                    match flags {
                        Flags::Given | Flags::Shared => {
                            self.drop_owned_value(env, elem_ptr, &element_ty)?;
                        }
                        Flags::Borrowed => {} // no-op
                        Flags::Uninitialized => {
                            anyhow::bail!("array_drop: element is uninitialized")
                        }
                    }
                } else {
                    // No flags (e.g., Int) — just uninitialize
                    self.uninitialize(env, elem_ptr, &element_ty)?;
                }

                self.free(env, &array_tv)?;
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Expr::ArrayInitialize(
                parameters,
                array_expr,
                index_expr,
                value_expr,
            ) => {
                let (_array_ty, element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.expect_int(&index_tv)? as usize;
                self.free(&stack_frame.env, &index_tv)?;
                let value_tv = self.eval_expr_value(stack_frame, value_expr)?;
                let env = &stack_frame.env;
                let element_size = self.size_of(env, &element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_initialize")?;

                let elem_ptr = Pointer {
                    index: array_ptr.index,
                    offset: 2 + index * element_size,
                };

                // Check that slot is currently uninitialized
                self.check_element_uninitialized(elem_ptr, "array_initialize")?;

                // Write value words at element offset.
                // Uninitialize value_tv first (ownership transferred to element)
                // so that free below doesn't double-drop the content.
                let words = self.read_words(value_tv.pointer, element_size);
                self.write_words(elem_ptr, &words);
                self.uninitialize(env, value_tv.pointer, &value_tv.ty)?;
                self.free(env, &value_tv)?;

                self.free(env, &array_tv)?;
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Expr::Panic => anyhow::bail!("panic!"),

            crate::grammar::Expr::Clear(var) => {
                let var_key = Var::Id(var.clone());
                if let Some(&ptr) = stack_frame.variables.get(&var_key) {
                    let env = &stack_frame.env;
                    let ty = env.var_ty(&var_key)?.clone();
                    self.uninitialize(env, ptr, &ty)?;
                }
                Ok(Outcome::Value(self.unit_value()))
            }
        }
    }

    /// Evaluate an expression, expecting a value (not early exit).
    /// Use this in positions where break/return would be nonsensical
    /// (e.g., function arguments, arithmetic operands).
    fn eval_expr_value(
        &mut self,
        stack_frame: &mut StackFrame,
        expr: &crate::grammar::Expr,
    ) -> anyhow::Result<TypedValue> {
        match self.eval_expr(stack_frame, expr)? {
            Outcome::Value(tv) => Ok(tv),
            Outcome::Break => anyhow::bail!("break outside of loop"),
            Outcome::Return(_) => anyhow::bail!("return in expression position"),
        }
    }
}

fn extract_size_of_ty(parameters: &[Parameter]) -> anyhow::Result<Ty> {
    match parameters {
        [Parameter::Ty(ty)] => Ok(ty.clone()),
        _ => anyhow::bail!("size_of requires exactly one type parameter"),
    }
}

/// Format a single word for heap dump output.
/// `hex_width` controls zero-padding for pointer indices.
fn fmt_word(word: &Word, hex_width: usize) -> String {
    match word {
        Word::Int(n) => format!("Int({n})"),
        Word::Flags(f) => format!("Flags({f:?})"),
        Word::RefCount(n) => format!("RefCount({n})"),
        Word::Capacity(n) => format!("Capacity({n})"),
        Word::Pointer(p) => {
            if p.offset == 0 {
                format!("Pointer(0x{:0>width$x})", p.index, width = hex_width)
            } else {
                format!(
                    "Pointer(0x{:0>width$x}+{})",
                    p.index,
                    p.offset,
                    width = hex_width
                )
            }
        }
        Word::Uninitialized => "Uninitialized".to_string(),
    }
}

/// Extract the element type T from Array[T] parameters.
fn extract_array_element_ty(parameters: &[Parameter]) -> anyhow::Result<Ty> {
    match parameters {
        [Parameter::Ty(ty)] => Ok(ty.clone()),
        _ => anyhow::bail!("Array requires exactly one type parameter"),
    }
}

/// Extract the element type T from Array[T] parameters and build the Array[T] type.
fn extract_array_ty(parameters: &[Parameter]) -> anyhow::Result<(Ty, Ty)> {
    let element_ty = extract_array_element_ty(parameters)?;
    let array_ty = Ty::NamedTy(NamedTy {
        name: TypeName::Array,
        parameters: parameters.to_vec(),
    });
    Ok((array_ty, element_ty))
}
