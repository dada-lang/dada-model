use std::sync::Arc;

use formality_core::{set, Map, Upcast};
use tracing::field;

use crate::grammar::{
    ClassDecl, ClassDeclBoundData, FieldId, MethodDeclBoundData, MethodId, NamedTy, Parameter,
    Perm, Place, Program, Ty, TypeName, ValueId, Var,
};

use crate::type_system::env::Env;
use crate::type_system::predicates::{
    self, prove_is_boxed, prove_is_copy, prove_is_mut, prove_is_owned,
};
use std::fmt::Write;

/// Result of evaluating a statement or expression.
enum Outcome {
    /// Normal result with a value.
    Value(ObjectValue),
    /// Break out of the innermost loop.
    Break,
    /// Return from the current method with a value.
    Return(ObjectValue),
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
    MutRef(Pointer),
    RefCount(i64),
    Capacity(usize),
    Uninitialized,
}
// ANCHOR_END: Word

// ANCHOR: Flags
/// Permission flag for unique objects.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Flags {
    /// Indicates that the object here was freed.
    /// This is used when dropping elements of an array to track.
    Uninitialized,

    /// Indicates that the data here is fully owned.
    Given,

    /// Indicates that the data here has shared ownership.
    Shared,

    /// Indicates that the data here is a borrowed reference.
    Borrowed,
}
// ANCHOR_END: Flags

/// A pointer that referes to an object's data and carries along flags.
#[derive(Clone)]
struct ObjectData {
    /// Points to the object's memory.
    ///
    /// NB: This always points at the object's **fields** (or array elements).
    ///
    /// For a boxed class like an array, this means we derefence the box.
    ///
    /// For a mut-ref, this means we derefrence the mut-ref.
    ///
    /// For an inline class, this means we skip over the flags (which will be incorporated
    /// into `flags`) and get the rest of the data at offset 1.
    pointer: Pointer,

    /// Effective permissions accumulated during travel.
    operms: ObjectPerms,

    /// The type of the object stored in this place (with permissions stripped).
    named_ty: NamedTy,
}

/// Effective permission accumulated during place resolution.
/// Distinct from `Flags` (which is stored in memory):
/// - `Given` is true identity — passthrough to runtime flags.
/// - `MutRef` means we traversed through a `mut[place]` indirection.
/// - `Shared`/`Borrowed` override inner runtime flags.
/// - `Uninitialized` is a fault.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ObjectPerms {
    Given,
    MutRef,
    Shared,
    Borrowed,
}

impl ObjectPerms {
    /// Compute the effective flags for a value, given its type.
    fn from_value_flags(env: &Env, ty: &Ty, flags: Flags) -> anyhow::Result<Self> {
        match flags {
            Flags::Uninitialized => {
                anyhow::bail!("access through uninitialized value")
            }
            Flags::Given => {
                if predicates::prove_is_mut(env, ty).is_proven() {
                    Ok(ObjectPerms::MutRef)
                } else {
                    Ok(ObjectPerms::Given)
                }
            }
            Flags::Shared => Ok(ObjectPerms::Shared),
            Flags::Borrowed => Ok(ObjectPerms::Borrowed),
        }
    }

    /// Apply `.mut` to the effective flags, if possible.
    /// This is an error if we have passed through a shared value.
    fn mut_ref(&self) -> anyhow::Result<ObjectPerms> {
        match self {
            ObjectPerms::Given => Ok(ObjectPerms::MutRef),
            ObjectPerms::MutRef => Ok(ObjectPerms::MutRef),
            ObjectPerms::Shared | ObjectPerms::Borrowed => {
                anyhow::bail!("access through mut-ref of shared/borrowed value")
            }
        }
    }

    /// Apply the flags that we loaded from the object when projecting.
    ///
    /// For example, if we are resolving a place `a.b.c` and we've just loaded
    /// the object for the flag `c`, then `self` would be the effective flags
    /// from `a.b`, and `object_flags` would be the flags we loaded from `c`,
    /// which might be given/shared/uninitialized etc.
    fn with_projection_flags(&self, prefix_flags: Flags) -> anyhow::Result<Self> {
        match (*self, prefix_flags) {
            // Loading uninitialized content is UB.
            (_, Flags::Uninitialized) => {
                anyhow::bail!("access through uninitialized value")
            }

            // Loading shared content copies shared content.
            (_, Flags::Shared) => Ok(ObjectPerms::Shared),

            // Loading borrowed content copies borrowed content.
            (_, Flags::Borrowed) => Ok(ObjectPerms::Borrowed),

            // Loading owned content preserves whatever flags we had.
            (flags, Flags::Given) => Ok(flags),
        }
    }
}

enum FieldPointer<'a> {
    MutRef(Pointer, &'a Ty),
    Boxed(Pointer, &'a Ty),
    Leaf(Pointer, &'a NamedTy),
}

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
/// For boxed types (e.g., arrays, mut-refs), this will be a pointer to a pointer.
/// For inline objects, this will be a pointer to the object data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectValue {
    pointer: Pointer,
    ty: Ty,
}
// ANCHOR_END: TypedValue

/// Categorize the possible layouts of an object value in memory.
enum ObjectValueLayout<'a> {
    /// This is a mutable reference; pointers should point to a `Word::MutRef`.
    MutRef(Pointer, &'a Ty),

    /// This is a boxed object; pointers should point to flags + pointer.
    Boxed(Pointer, &'a Ty),

    /// This is a flat object; pointers should point directly to the fields.
    Flat(Pointer, &'a Ty),
}

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
    fn unit_value(&mut self) -> ObjectValue {
        ObjectValue {
            pointer: self.alloc_unit(),
            ty: Ty::unit(),
        }
    }

    /// Read one word at a pointer.
    fn read_word(&self, ptr: Pointer) -> Word {
        self.allocs[ptr.index].data[ptr.offset]
    }

    /// Assert that the value at `pointer` is a capacity word and return the capacity.
    fn read_int(&self, pointer: Pointer) -> anyhow::Result<i64> {
        match self.read_word(pointer) {
            Word::Int(n) => Ok(n),
            other => anyhow::bail!("expected Int word, got {other:?}"),
        }
    }

    /// Assert that the value at `pointer` is a capacity word and return the capacity.
    fn into_int_value(&self, value: &ObjectValue) -> anyhow::Result<i64> {
        match self.named_ty(&value.ty).name {
            TypeName::Int => (),
            _ => {
                anyhow::bail!("expected Int value, got {:?}", value.ty)
            }
        }
        let v = self.read_int(value.pointer)?;
        self.drop_value(&stack_frame.env, value)?;
        Ok(v)
    }

    /// Assert that the value at `pointer` is a capacity word and return the capacity.
    fn read_capacity(&self, pointer: Pointer) -> anyhow::Result<usize> {
        match self.read_word(pointer) {
            Word::Capacity(n) => Ok(n),
            other => anyhow::bail!("expected Capacity word, got {other:?}"),
        }
    }

    /// Assert that the value at `pointer` is a mut-ref and return the inner pointer.
    fn read_mut_ref(&self, pointer: Pointer) -> anyhow::Result<Pointer> {
        match self.read_word(pointer) {
            Word::MutRef(n) => Ok(n),
            other => anyhow::bail!("expected MutRef word, got {other:?}"),
        }
    }

    /// Set `count` words at `ptr` to `Word::Uninitialized`.
    fn uninitialize_words(&mut self, ptr: Pointer, count: usize) -> anyhow::Result<()> {
        for i in 0..count {
            self.uninitialize_word(ptr + i)?;
        }
        Ok(())
    }

    /// Set the word at `ptr` to `Word::Uninitialized`.
    fn uninitialize_word(&mut self, ptr: Pointer) -> anyhow::Result<()> {
        if let Word::Uninitialized = self.read_word(ptr) {
            anyhow::bail!("access of value");
        }
        self.write_word(ptr, Word::Uninitialized);
        Ok(())
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

    fn value_layout<'v>(
        &self,
        env: &Env,
        value: &'v ObjectValue,
    ) -> anyhow::Result<ObjectValueLayout<'v>> {
        if self.is_mut_ref_type(env, &value.ty) {
            Ok(ObjectValueLayout::MutRef(value.pointer, &value.ty))
        } else if self.is_boxed_type(env, &value.ty) {
            Ok(ObjectValueLayout::Boxed(value.pointer, &value.ty))
        } else {
            Ok(ObjectValueLayout::Flat(value.pointer, &value.ty))
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
        let class_ty = NamedTy {
            name: class_name.upcast(),
            parameters: parameters.to_vec(),
        };
        let mut offset = 0;
        for field in &class_data.fields {
            if field.name == *field_id {
                return Ok((offset, field.ty.clone()));
            }
            offset += self.size_of(env, &field.ty)?;
        }
        anyhow::bail!("no field `{field_id:?}` in class `{class_name:?}`")
    }

    /// Check if a type is owned (delegates to the type system).
    fn is_owned_type(&self, env: &Env, ty: impl Upcast<Ty>) -> bool {
        let ty = ty.upcast();
        prove_is_owned(env, ty).is_proven()
    }

    /// Check if a type is copy (delegates to the type system).
    fn is_copy_type(&self, env: &Env, ty: impl Upcast<Ty>) -> bool {
        let ty = ty.upcast();
        prove_is_copy(env, ty).is_proven()
    }

    /// Compute the size (in words) of a type.
    fn size_of(&self, env: &Env, ty: &Ty) -> anyhow::Result<usize> {
        if self.is_mut_ref_type(env, ty) {
            Ok(1)
        } else {
            self.size_of_named_ty(env, &self.named_ty(ty))
        }
    }

    /// Compute the size (in Words) of a type.
    fn size_of_named_ty(&self, env: &Env, named_ty: &NamedTy) -> anyhow::Result<usize> {
        let NamedTy { name, parameters } = named_ty;
        match name {
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

                let mut total = 0;
                for field in &fields {
                    total += self.size_of(env, &field.ty)?;
                }

                Ok(total)
            }
        }
    }

    // ---------------------------------------------------------------
    // Core value operations
    // ---------------------------------------------------------------

    /// Copy the data for an object into a new value.
    fn copy_object_data(&mut self, env: &Env, object_data: &ObjectData) -> anyhow::Result<Pointer> {
        if self.is_boxed_type(env, &object_data.named_ty) {
            // For a boxed object (e.g., array), we copy the pointer and give a "Flags Given" to start.
            // A later pass will update the flags.
            Ok(self.alloc_raw(Alloc {
                data: vec![
                    Word::Flags(Flags::Given),
                    Word::Pointer(object_data.pointer),
                ],
            }))
        } else {
            // For a flat object, we copy all words and omit flags word
            let size = self.size_of_named_ty(env, &object_data.named_ty)?;
            let words = self.read_words(object_data.pointer, size);
            Ok(self.alloc_raw(Alloc { data: words }))
        }
    }

    /// Mark a value as uninitialized.
    /// Sets the flags word to Flags::Uninitialized (if present) and
    /// overwrites all remaining data words with Word::Uninitialized.
    fn uninitialize(&mut self, env: &Env, value: &ObjectValue) -> anyhow::Result<()> {
        // MutRef: single word, just overwrite.
        if self.is_mut_ref_type(env, &value.ty) {
            self.write_word(value.pointer, Word::Uninitialized);
            return Ok(());
        } else if self.is_boxed_type(env, &value.ty) {
            self.write_flag_word(value.pointer, Flags::Uninitialized);
            self.write_word(value.pointer + 1, Word::Uninitialized);
        } else {
            let size = self.size_of(env, &value.ty)?;
            for i in 0..size {
                self.write_word(value.pointer + i, Word::Uninitialized);
            }
        }
        Ok(())
    }

    /// Read the flags of a value, if it has them.
    fn read_flag_word(&self, ptr: Pointer) -> anyhow::Result<Flags> {
        // MutRef types have no flags word — they are a single Word::MutRef.
        match self.read_word(ptr) {
            Word::Flags(f) => Ok(f),
            other => anyhow::bail!("expected Flags word, got {other:?}"),
        }
    }

    /// Write flags for a value.
    fn write_flag_word(&mut self, ptr: Pointer, flags: Flags) -> anyhow::Result<()> {
        let old_value = self.read_word(ptr);
        assert!(
            matches!(old_value, Word::Flags(_)),
            "asked to write flags to a memory spot that does not contain flags: {old_value:?}"
        );
        self.write_word(ptr, Word::Flags(flags));
        Ok(())
    }

    /// Extract the allocation pointer from an Array TypedValue.
    fn expect_flags(&self, ptr: Pointer) -> anyhow::Result<Flags> {
        match self.read_word(ptr) {
            Word::Flags(Flags::Uninitialized) => anyhow::bail!("access of uninitialized array"),
            Word::Flags(flags) => Ok(flags),
            other => anyhow::bail!("error: expected Flags word for array, got {:?}", other),
        }
    }

    /// Extract the allocation pointer from an Array TypedValue.
    fn expect_object_pointer(&self, ptr: Pointer) -> anyhow::Result<(Flags, Pointer)> {
        let flags = self.expect_flags(ptr)?;
        let ptr_word = self.read_word(ptr + 1);
        match ptr_word {
            Word::Pointer(alloc_ptr) => Ok((flags, alloc_ptr)),
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

    /// Convert a value from Given to Shared ownership in place.
    /// Called by Expr::Share. Flips only the outermost flags word.
    /// Inner fields keep their runtime flags — the type system
    /// (via resolve_place) enforces shared semantics on traversal.
    fn traverse_value(
        &mut self,
        env: &Env,
        value: &ObjectValue,
        op: &mut impl FnMut(&mut Self, &Env, FieldPointer<'_>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        match self.value_layout(env, value)? {
            // No updates needed for borrowed data.
            ObjectValueLayout::MutRef(pointer, ty) => {
                op(self, env, FieldPointer::MutRef(pointer, ty))
            }
            ObjectValueLayout::Boxed(pointer, ty) => {
                op(self, env, FieldPointer::Boxed(pointer, ty))
            }
            ObjectValueLayout::Flat(pointer, ty) => {
                self.traverse_object_fields(env, pointer, &self.named_ty(ty), op)
            }
        }
    }

    /// Convert a value from Given to Shared ownership in place.
    /// Called by Expr::Share. Flips only the outermost flags word.
    /// Inner fields keep their runtime flags — the type system
    /// (via resolve_place) enforces shared semantics on traversal.
    fn traverse_object_fields(
        &mut self,
        env: &Env,
        object_data_pointer: Pointer,
        object_ty: &NamedTy,
        op: &mut impl FnMut(&mut Self, &Env, FieldPointer<'_>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        let (field_pointer, field_tys) = self.find_object_fields(object_data_pointer, object_ty)?;
        let mut offset = 0;
        if field_tys.is_empty() {
            op(self, env, FieldPointer::Leaf(field_pointer, object_ty))
        } else {
            for field_ty in field_tys {
                self.traverse_value(
                    env,
                    &ObjectValue {
                        pointer: field_pointer + offset,
                        ty: field_ty.clone(),
                    },
                    op,
                )?;
                let field_size = self.size_of(env, &field_ty)?;
                offset += field_size;
            }
            Ok(())
        }
    }

    /// Given a pointer to an object's data, return the pointer to the first field and the types of all fields.
    fn find_object_fields(
        &mut self,
        object_data_pointer: Pointer,
        object_ty: &NamedTy,
    ) -> Result<(Pointer, Vec<Ty>), anyhow::Error> {
        let NamedTy { name, parameters } = object_ty;
        Ok(match name {
            TypeName::Tuple(_) => (
                object_data_pointer,
                parameters
                    .into_iter()
                    .map(|p| p.as_ty().expect("tuple parameters to be types").clone())
                    .collect(),
            ),
            TypeName::Int => (object_data_pointer, vec![]),
            TypeName::Array => {
                let capacity = self.read_capacity(object_data_pointer + 1)?;
                let element_ty = extract_array_element_ty(parameters)?;
                let element_tys = (0..capacity).map(|_| element_ty.clone()).collect();
                (object_data_pointer + 2, element_tys)
            }
            TypeName::Id(class_name) => {
                let class_decl = self.program.class_named(&class_name)?;
                let class_data = class_decl.binder.instantiate_with(&parameters)?;
                (
                    object_data_pointer,
                    class_data
                        .fields
                        .into_iter()
                        .map(|field| field.ty)
                        .collect(),
                )
            }
        })
    }

    /// Set the flags of a heap value to Shared, without modifying refcounts.
    fn and_convert_given_to_shared(
        &mut self,
        _env: &Env,
        field_pointer: FieldPointer<'_>,
    ) -> anyhow::Result<()> {
        match field_pointer {
            FieldPointer::MutRef(..) | FieldPointer::Leaf(..) => {
                // No action needed if there is no owned boxed value, the type
                // system knows that we don't own this value, just copy it.
            }
            FieldPointer::Boxed(pointer, _ty) => {
                let (flags, _heap_pointer) = self.expect_object_pointer(pointer)?;
                match flags {
                    Flags::Uninitialized => anyhow::bail!("sharing uninitialized object"),
                    Flags::Borrowed | Flags::Shared => {
                        // No updates needed for borrowed or shared data.
                    }
                    Flags::Given => {
                        self.write_flag_word(pointer, Flags::Shared);
                    }
                }
            }
        }
        Ok(())
    }

    /// *Referencing* a boxed object makes given into borrowed
    /// but for shared it increments the refcount.
    ///
    /// Intended for use with `for_each_owned_heap_value`.
    fn and_ref_fields_owned_elsewhere(
        &mut self,
        _env: &Env,
        field_pointer: FieldPointer<'_>,
    ) -> anyhow::Result<()> {
        match field_pointer {
            FieldPointer::MutRef(..) | FieldPointer::Leaf(..) => {
                // No action needed if there is no owned boxed value, the type
                // system knows that we don't own this value, just copy it.
            }
            FieldPointer::Boxed(pointer, _ty) => {
                let (flags, heap_pointer) = self.expect_object_pointer(pointer)?;
                match flags {
                    Flags::Uninitialized => anyhow::bail!("sharing uninitialized object"),
                    Flags::Borrowed => {
                        // No updates needed for borrowed data.
                    }
                    Flags::Given => {
                        self.write_flag_word(pointer, Flags::Borrowed);
                    }
                    Flags::Shared => {
                        let refcount = self.read_refcount(heap_pointer)?;
                        self.write_refcount(heap_pointer, refcount + 1);
                    }
                }
            }
        }
        Ok(())
    }

    /// Set the flags of a heap value to Shared and increments refcounts.
    ///
    /// Intended for use with `for_each_owned_heap_value`.
    fn and_copy_shared_fields(
        &mut self,
        _env: &Env,
        field_pointer: FieldPointer<'_>,
    ) -> anyhow::Result<()> {
        match field_pointer {
            FieldPointer::MutRef(..) | FieldPointer::Leaf(..) => {
                // No action needed if there is no owned boxed value, the type
                // system knows that we don't own this value, just copy it.
            }
            FieldPointer::Boxed(pointer, ty) => {
                let (flags, heap_pointer) = self.expect_object_pointer(pointer)?;
                match flags {
                    Flags::Uninitialized => anyhow::bail!("sharing uninitialized object"),
                    Flags::Borrowed => {
                        // No updates needed for borrowed data.
                    }
                    Flags::Given | Flags::Shared => {
                        self.write_flag_word(pointer, Flags::Shared);
                        let refcount = self.read_refcount(heap_pointer)?;
                        self.write_refcount(heap_pointer, refcount + 1);
                    }
                }
            }
        }

        Ok(())
    }

    /// Set the flags of a heap value to uninitialized and clear the pointer itself.
    /// Equivalent of writing null.
    fn and_uninitialize_fields(
        &mut self,
        env: &Env,
        field_pointer: FieldPointer<'_>,
    ) -> anyhow::Result<()> {
        match field_pointer {
            FieldPointer::Boxed(pointer, _ty) => {
                let (flags, _heap_pointer) = self.expect_object_pointer(pointer)?;
                match flags {
                    Flags::Uninitialized => anyhow::bail!("sharing uninitialized object"),
                    Flags::Borrowed | Flags::Given | Flags::Shared => {
                        self.write_flag_word(pointer, Flags::Uninitialized);
                    }
                }
                self.uninitialize_word(pointer + 1);
            }

            FieldPointer::MutRef(pointer, _) => self.uninitialize_word(pointer)?,

            FieldPointer::Leaf(pointer, ty) => {
                let size = self.size_of_named_ty(env, ty)?;
                self.uninitialize_words(pointer, size)?;
            }
        }

        Ok(())
    }

    /// Drop the contents of an owned object.
    ///
    /// Intended for use with `for_each_owned_heap_value` when we copy a shared place.
    fn and_drop_fields(
        &mut self,
        env: &Env,
        field_pointer: FieldPointer<'_>,
    ) -> anyhow::Result<()> {
        match field_pointer {
            FieldPointer::Boxed(pointer, ty) => {
                let (flags, heap_pointer) = self.expect_object_pointer(pointer)?;
                match flags {
                    Flags::Uninitialized => anyhow::bail!("sharing uninitialized object"),
                    Flags::Borrowed => {
                        // No updates needed for borrowed data.
                    }
                    Flags::Given | Flags::Shared => {
                        let refcount = self.read_refcount(heap_pointer)?;
                        anyhow::ensure!(refcount > 0, "drop_array: refcount already zero");
                        let new_refcount = refcount - 1;
                        self.write_refcount(heap_pointer, new_refcount);

                        if new_refcount == 0 {
                            self.drop_object_data(
                                env,
                                &ObjectData {
                                    pointer,
                                    operms: ObjectPerms::Given,
                                    named_ty: self.named_ty(ty),
                                },
                            )?;
                        }
                    }
                }
                self.uninitialize_words(pointer, 2)?;
            }

            FieldPointer::MutRef(pointer, _) => self.uninitialize_word(pointer)?,

            FieldPointer::Leaf(pointer, ty) => {
                let size = self.size_of_named_ty(env, ty)?;
                self.uninitialize_words(pointer, size)?;
            }
        }

        Ok(())
    }

    /// Drop an owned value (Given or Shared): recursively drop owned fields,
    /// then uninitialize. Given and Shared converge at every leaf — a Given
    /// array with refcount 1 decrements the same way as a Shared array.
    fn drop_value(&mut self, env: &Env, value: &ObjectValue) -> anyhow::Result<()> {
        self.traverse_value(env, value, &mut Self::and_drop_fields)
    }

    /// Drop the fields of an object.
    fn drop_object_data(&mut self, env: &Env, object_data: &ObjectData) -> anyhow::Result<()> {
        self.traverse_object_fields(
            env,
            object_data.pointer,
            &object_data.named_ty,
            &mut Self::and_drop_fields,
        )
    }

    /// Check if a type is a mut[place] reference type.
    fn is_mut_ref_type(&self, env: &Env, ty: &Ty) -> bool {
        prove_is_mut(env, ty).is_proven()
    }

    /// Check if a type is a boxed type (e.g., an array).
    ///
    /// Boxed types are stored like `(flags, pointer-to-fields)` instead of
    /// `(flags, ...fields)`.
    fn is_boxed_type(&self, env: &Env, ty: impl Upcast<Ty>) -> bool {
        let ty = ty.upcast();
        prove_is_boxed(env, ty).is_proven()
    }

    /// Return the named type from `ty`, stripping permissions.
    /// The interpreter only works with fully monomorphized types, so this should always succeed.
    fn named_ty(&self, ty: &Ty) -> NamedTy {
        ty.named_ty().expect("monomorphized types")
    }

    // ---------------------------------------------------------------
    // Place access operations
    // ---------------------------------------------------------------

    /// `place.give`: copy/move a value out of a place.
    ///
    /// `place_ty` is the runtime type (with Perm::Mt stripped when the place
    /// was reached through a MutRef traversal). `original_place_ty` is the
    /// un-stripped type from `env.place_ty()`, used for the MutRef result type.
    fn give_place(
        &mut self,
        env: &Env,
        object_data: ObjectData,
        place: &Place,
    ) -> anyhow::Result<ObjectValue> {
        match object_data.operms {
            ObjectPerms::Given => {
                let copied = self.copy_object_data(env, &object_data)?;
                self.traverse_object_fields(
                    env,
                    object_data.pointer,
                    &object_data.named_ty,
                    &mut Self::and_uninitialize_fields,
                )?;
                Ok(ObjectValue {
                    pointer: copied,
                    ty: object_data.named_ty.upcast(),
                })
            }
            ObjectPerms::MutRef => self.mut_place(env, object_data, place),
            ObjectPerms::Shared => {
                let result_ty = Ty::apply_perm(Perm::Shared, &object_data.named_ty);
                let copied = self.copy_object_data(env, &object_data)?;
                let shared_value = ObjectValue {
                    pointer: copied,
                    ty: result_ty,
                };
                self.traverse_value(env, &shared_value, &mut Self::and_copy_shared_fields)?;
                Ok(shared_value)
            }
            ObjectPerms::Borrowed => self.ref_place(env, object_data, place),
        }
    }

    /// `place.ref`: create a borrowed reference to a place.
    fn ref_place(
        &mut self,
        env: &Env,
        object_data: ObjectData,
        place: &crate::grammar::Place,
    ) -> anyhow::Result<ObjectValue> {
        let result_ty = Ty::apply_perm(Perm::rf(set![place]), &object_data.named_ty);
        let copied = self.copy_object_data(env, &object_data)?;
        let shared_value = ObjectValue {
            pointer: copied,
            ty: result_ty,
        };
        self.traverse_value(
            env,
            &shared_value,
            &mut Self::and_ref_fields_owned_elsewhere,
        )?;
        Ok(shared_value)
    }

    /// `place.mut`: create a mutable reference (MutRef) to a place.
    fn mut_place(
        &mut self,
        _env: &Env,
        object_data: ObjectData,
        place: &crate::grammar::Place,
    ) -> anyhow::Result<ObjectValue> {
        let new_ptr = self.alloc_raw(Alloc {
            data: vec![Word::MutRef(object_data.pointer)],
        });
        return Ok(ObjectValue {
            pointer: new_ptr,
            ty: Ty::apply_perm(Perm::mt(set![place]), &object_data.named_ty),
        });
    }

    /// `place.drop`: drop a value at a place.
    fn drop_place(&mut self, env: &Env, object_data: ObjectData) -> anyhow::Result<ObjectValue> {
        match object_data.operms {
            ObjectPerms::Given | ObjectPerms::Shared => {
                self.drop_object_data(env, &object_data)?;
            }
            ObjectPerms::MutRef | ObjectPerms::Borrowed => {
                // Neither MutRef nor Borrowed: we don't own the data, so no-op
                // on the referent. The MutRef word itself is scrubbed
                // when the variable holding it goes out of scope.
            }
        }
        Ok(self.unit_value())
    }

    /// Resolve a place expression to a an object and some effective
    /// permissions to that object, returning a [`ResolvedPlace`].
    fn resolve_place_to_object_data(
        &self,
        stack_frame: &StackFrame,
        place: &crate::grammar::Place,
    ) -> anyhow::Result<ObjectData> {
        let var_ptr = *stack_frame
            .variables
            .get(&place.var)
            .ok_or_else(|| anyhow::anyhow!("undefined variable `{:?}`", place.var))?;

        let env = &stack_frame.env;

        // The value of the place so far. This starts as the
        // variable's value and then we load the value of each
        // field progressively.
        let mut place_value = ObjectValue {
            pointer: var_ptr,
            ty: env.var_ty(&place.var)?.clone(),
        };

        // The permissions of the object that owns `place_value`;
        // initlaly "given" to represent the stack frame owning the variable.
        let mut owner_operms = ObjectPerms::Given;

        for projection in &place.projections {
            // Get an object from the prefix value
            let owner_data = self.object_value_to_data(env, &place_value, owner_operms)?;

            // Compute the pointer to the field and the (declared) type of the field.
            let field_value = self.resolve_projection(env, &owner_data, projection)?;

            // Update owner value to be the value from the field
            // and update the permissions to be the last object
            place_value = field_value;
            owner_operms = owner_data.operms;
        }

        self.object_value_to_data(env, &place_value, owner_operms)
    }

    /// If this place stores a `mut[ty]` *directly*, then dereference it.
    /// The type of `place_ty` must be the type of the variable or field being projected,
    /// not the "effective" type as seen by the user.
    ///
    /// For example, given
    ///
    /// ```dada
    /// class Outer { inner: Inner }
    ///
    /// p: mut Outer
    /// ```
    ///
    /// IF you access `p.inner`, this would be invoked first with
    /// the type of `p` (`mut Outer`), which would trigger a deref,
    /// but then with the type of the field `Outer.Inner` (`given Inner`),
    /// which would not.
    ///
    /// In comparison, given
    ///
    /// ```dada
    /// class Outer[perm P] { inner: P Inner }
    ///
    /// p: Outer[mut]
    /// ```
    ///
    /// the first call would be with a `given` (no deref trigger),
    /// but the second be given `mut Inner`, which would trigger a deref.
    fn object_value_to_data(
        &self,
        env: &Env,
        value: &ObjectValue,
        owner_operms: ObjectPerms,
    ) -> anyhow::Result<ObjectData> {
        let named_ty = self.named_ty(&value.ty);
        if self.is_mut_ref_type(env, &value.ty) {
            let mut_pointer = self.read_mut_ref(value.pointer)?;
            Ok(ObjectData {
                pointer: mut_pointer,
                operms: owner_operms.mut_ref()?,
                named_ty,
            })
        } else if self.is_boxed_type(env, &value.ty) {
            let (object_flags, object_data) = self.expect_object_pointer(value.pointer)?;
            Ok(ObjectData {
                pointer: object_data,
                operms: owner_operms.with_projection_flags(object_flags)?,
                named_ty,
            })
        } else if self.is_copy_type(env, &value.ty) {
            if self.is_owned_type(env, &value.ty) {
                // If this is copy and owned, it is shared
                Ok(ObjectData {
                    pointer: value.pointer,
                    operms: owner_operms.with_projection_flags(Flags::Shared)?,
                    named_ty,
                })
            } else {
                // Otherwise it is a ref
                Ok(ObjectData {
                    pointer: value.pointer,
                    operms: owner_operms.with_projection_flags(Flags::Borrowed)?,
                    named_ty,
                })
            }
        } else {
            // If this is move and *not* a mut-ref, it must be given
            Ok(ObjectData {
                pointer: value.pointer,
                operms: owner_operms,
                named_ty,
            })
        }
    }

    /// Given a pointer to an object and its type, resolve a single projection
    /// (e.g., `.field`) to get the pointer and declared type of the projected element.
    fn resolve_projection(
        &self,
        env: &Env,
        owner_object: &ObjectData,
        projection: &crate::grammar::Projection,
    ) -> anyhow::Result<ObjectValue> {
        match projection {
            crate::grammar::Projection::Field(field_id) => match &owner_object.named_ty {
                NamedTy {
                    name: TypeName::Id(class_name),
                    parameters,
                } => {
                    let (field_offset, field_ty) =
                        self.field_offset_by_name(env, class_name, parameters, field_id)?;
                    Ok(ObjectValue {
                        pointer: Pointer {
                            index: owner_object.pointer.index,
                            offset: owner_object.pointer.offset + field_offset,
                        },
                        ty: field_ty,
                    })
                }
                _ => anyhow::bail!(
                    "field access on non-class type: {:?}",
                    owner_object.named_ty
                ),
            },
        }
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
    pub fn display_value(&self, env: &Env, tv: &ObjectValue) -> String {
        let mut buf = String::new();
        self.fmt_value(env, &mut buf, tv.pointer, &tv.ty);
        buf
    }

    fn fmt_value(&self, env: &Env, buf: &mut String, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        // MutRef: dereference and display the underlying value.
        if let Ty::ApplyPerm(perm @ Perm::Mt(_), inner) = ty {
            write!(buf, "{perm:?} ").unwrap();
            match self.read_word(ptr) {
                Word::MutRef(inner_ptr) => {
                    self.fmt_value(env, buf, inner_ptr, inner);
                }
                Word::Uninitialized => write!(buf, "uninitialized").unwrap(),
                other => write!(buf, "<unexpected: {other:?}>").unwrap(),
            }
            return Ok(());
        }

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
                Word::Int(n) => write!(buf, "{n}")?,
                Word::Uninitialized => write!(buf, "uninitialized")?,
                other => write!(buf, "<unexpected: {other:?}>")?,
            },

            Ty::NamedTy(NamedTy {
                name: TypeName::Tuple(0),
                ..
            }) => {
                // Unit: zero words, nothing to display
                write!(buf, "()")?;
            }

            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name)?;
                let class_data = class_decl.binder.instantiate_with(parameters)?;

                write!(buf, "{class_name:?}")?;
                write!(buf, " {{ ")?;

                let mut offset = 0;
                for (field, index) in class_data.fields.iter().zip(0..) {
                    if index > 0 {
                        write!(buf, ", ")?;
                    }
                    write!(buf, "{:?}: ", field.name)?;
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    self.fmt_value(env, buf, field_ptr, &field.ty)?;
                    offset += self.size_of(env, &field.ty).unwrap();
                }

                write!(buf, " }}")?;
            }

            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                parameters,
            }) => {
                let element_ty = extract_array_element_ty(parameters)?;
                let flags = self.expect_flags(ptr)?;
                if flags == Flags::Uninitialized {
                    write!(buf, "uninitialized")?;
                    return Ok(());
                }
                let array_ptr = match self.read_word(Pointer {
                    index: ptr.index,
                    offset: ptr.offset + 1,
                }) {
                    Word::Pointer(p) => p,
                    other => {
                        write!(buf, "<unexpected pointer: {other:?}>")?;
                        return Ok(());
                    }
                };
                write!(buf, "Array {{ flag: {flags:?}")?;
                let refcount = self.read_refcount(array_ptr).unwrap_or(-1);
                write!(buf, ", rc: {refcount}")?;
                let Word::Capacity(capacity) = self.read_word(Pointer {
                    index: array_ptr.index,
                    offset: 1,
                }) else {
                    write!(buf, ", <bad capacity> }}")?;
                    return Ok(());
                };
                let element_size = self.size_of(env, &element_ty).unwrap();
                for i in 0..capacity as usize {
                    write!(buf, ", ")?;
                    let elem_ptr = Pointer {
                        index: array_ptr.index,
                        offset: 2 + i * element_size,
                    };
                    self.fmt_value(env, buf, elem_ptr, &element_ty)?;
                }
                write!(buf, " }}")?;
            }

            Ty::NamedTy(NamedTy {
                name: TypeName::Tuple(_),
                ..
            }) => {
                // Non-unit tuples: display raw word representation
                write!(buf, "<tuple>")?;
            }
            Ty::Var(_) | Ty::ApplyPerm(..) => {
                unreachable!("fmt_value called on non-concrete type: {inner_ty:?}")
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------
    // Instantiation
    // ---------------------------------------------------------------

    fn instantiate_class(
        &mut self,
        env: &Env,
        class_name: &ValueId,
        parameters: &[Parameter],
        field_values: &[ObjectValue],
    ) -> anyhow::Result<ObjectValue> {
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
        Ok(ObjectValue { pointer: ptr, ty })
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
        this: ObjectValue,
        input_values: Vec<ObjectValue>,
    ) -> anyhow::Result<ObjectValue> {
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
            stack_frame.env = stack_frame
                .env
                .push_local_variable(var.clone(), input_value.ty)?;
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
                    let tv = ObjectValue { pointer: *ptr, ty };
                    self.drop_value(env, &tv)?;
                }
                Ok(result_tv)
            }
        }
    }

    // ---------------------------------------------------------------
    // Evaluation
    // ---------------------------------------------------------------

    /// Run a program by instantiating `Main()` and calling `main`.
    pub fn interpret(&mut self) -> anyhow::Result<ObjectValue> {
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
                    self.drop_value(&stack_frame.env, &final_value)?;
                    final_value = tv;
                }
                early @ (Outcome::Break | Outcome::Return(_)) => {
                    self.drop_value(&stack_frame.env, &final_value)?;
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
                let env = &stack_frame.env;

                if let Some((owner_place, last_projection)) = place.owner_field() {
                    // Field reassignment: resolve the prefix to an object,
                    // then compute the field offset for the last projection.
                    let owner_object_data =
                        self.resolve_place_to_object_data(stack_frame, &owner_place)?;
                    let field_value =
                        self.resolve_projection(env, &owner_object_data, &last_projection)?;

                    // Drop the old value at the field before overwriting.
                    self.drop_value(
                        env,
                        &ObjectValue {
                            pointer: field_value.pointer,
                            ty: field_value.ty.clone(),
                        },
                    )?;

                    // Bitwise copy: ownership moves into the field.
                    let size = self.size_of(env, &field_value.ty)?;
                    let words = self.read_words(tv.pointer, size);
                    self.write_words(field_value.pointer, &words);
                } else {
                    // Variable reassignment: overwrite the variable directly.
                    let var_ty = env.var_ty(&place.var)?;
                    let var_ptr = *stack_frame
                        .variables
                        .get(&place.var)
                        .ok_or_else(|| anyhow::anyhow!("undefined variable `{:?}`", place.var))?;

                    // Drop the old value before overwriting.
                    self.drop_value(
                        env,
                        &ObjectValue {
                            pointer: var_ptr,
                            ty: var_ty.clone(),
                        },
                    )?;

                    // Bitwise copy: ownership moves into the variable.
                    let size = self.size_of(env, &var_ty)?;
                    let words = self.read_words(tv.pointer, size);
                    self.write_words(var_ptr, &words);
                }

                // Scrub the temp without dropping — ownership was transferred.
                self.uninitialize(env, &tv)?;
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Statement::Loop(body) => loop {
                match self.eval_expr(stack_frame, body)? {
                    Outcome::Value(tv) => {
                        self.drop_value(&stack_frame.env, &tv)?;
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
                self.drop_value(&stack_frame.env, &tv)?;
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
            crate::grammar::Expr::Integer(n) => Ok(Outcome::Value(ObjectValue {
                pointer: self.alloc_int(*n as i64),
                ty: Ty::int(),
            })),

            crate::grammar::Expr::Add(lhs, rhs) => {
                let l = self.eval_expr_value(stack_frame, lhs)?;
                let r = self.eval_expr_value(stack_frame, rhs)?;
                let a = self.into_int_value(&l)?;
                let b = self.into_int_value(&r)?;
                let env = &stack_frame.env;
                Ok(Outcome::Value(ObjectValue {
                    pointer: self.alloc_int(a + b),
                    ty: Ty::int(),
                }))
            }

            crate::grammar::Expr::Block(block) => self.eval_block(stack_frame, block),

            crate::grammar::Expr::Tuple(exprs) => {
                for expr in exprs {
                    let tv = self.eval_expr_value(stack_frame, expr)?;
                    self.drop_value(&stack_frame.env, &tv)?;
                }
                Ok(Outcome::Value(ObjectValue {
                    pointer: self.alloc_raw(Alloc { data: vec![] }),
                    ty: Ty::unit(),
                }))
            }

            crate::grammar::Expr::New(class_name, params, field_exprs) => {
                let field_values: Vec<ObjectValue> = field_exprs
                    .iter()
                    .map(|e| self.eval_expr_value(stack_frame, e))
                    .collect::<Result<_, _>>()?;
                let env = &stack_frame.env;
                let result = self.instantiate_class(env, class_name, params, &field_values)?;
                for fv in &field_values {
                    // Scrub the temp without dropping — ownership moved into the class.
                    self.uninitialize(env, fv)?;
                }
                Ok(Outcome::Value(result))
            }

            crate::grammar::Expr::Place(crate::grammar::PlaceExpr { place, access }) => {
                let resolved = self.resolve_place_to_object_data(stack_frame, place)?;
                let env = &stack_frame.env;
                let tv = match access {
                    crate::grammar::Access::Gv => self.give_place(env, resolved, place)?,
                    crate::grammar::Access::Rf => self.ref_place(env, resolved, place)?,
                    crate::grammar::Access::Mt => self.mut_place(env, resolved, place)?,
                    crate::grammar::Access::Drop => self.drop_place(env, resolved)?,
                };
                Ok(Outcome::Value(tv))
            }

            crate::grammar::Expr::Share(expr) => {
                let tv = self.eval_expr_value(stack_frame, expr)?;
                let env = &stack_frame.env;
                self.traverse_value(env, &tv, &mut Self::and_convert_given_to_shared)?;
                Ok(Outcome::Value(tv))
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
                let arg_vals: Vec<ObjectValue> = args
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
                let n = self.into_int_value(&cond_tv)?;
                if n != 0 {
                    self.eval_expr(stack_frame, if_true)
                } else {
                    self.eval_expr(stack_frame, if_false)
                }
            }

            crate::grammar::Expr::SizeOf(parameters) => {
                let ty = extract_size_of_ty(parameters)?;
                let size = self.size_of(&stack_frame.env, &ty)?;
                Ok(Outcome::Value(ObjectValue {
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
                let length = self.into_int_value(&length_tv)?;
                anyhow::ensure!(length >= 0, "array_new: negative length {length}");
                let length = length as usize;
                let env = &stack_frame.env;
                let element_size = self.size_of(env, &element_ty)?;

                // Allocate: [Int(refcount), Int(length), element_slots...]
                // Each element slot has Flags::Uninitialized if the element type has flags,
                // otherwise Word::Uninitialized for all words.
                let mut data = vec![Word::RefCount(1), Word::Capacity(length)];
                for _ in 0..length {
                    data.extend(std::iter::repeat(Word::Uninitialized).take(element_size));
                }
                let alloc_ptr = self.alloc_raw(Alloc { data });

                let value_ptr = self.alloc_raw(Alloc {
                    data: vec![Word::Flags(Flags::Given), Word::Pointer(alloc_ptr)],
                });
                Ok(Outcome::Value(ObjectValue {
                    pointer: value_ptr,
                    ty: array_ty,
                }))
            }

            crate::grammar::Expr::ArrayCapacity(parameters, array_expr) => {
                let (_array_ty, _element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                // FIXME: we should check that the array's element type matches the expected type
                let (_array_flags, array_ptr) = self.expect_object_pointer(array_tv.pointer)?;
                let capacity = self.read_word(array_ptr + 1);
                self.drop_value(&stack_frame.env, &array_tv)?;
                match capacity {
                    Word::Capacity(n) => Ok(Outcome::Value(ObjectValue {
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
                let (array_flags, array_ptr) = self.expect_object_pointer(array_tv.pointer)?;

                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.into_int_value(&index_tv)? as usize;

                let env = &stack_frame.env;
                let element_size = self.size_of(env, &element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_give")?;

                let elem_ptr = array_ptr.index + 2 + index * element_size;

                // Propagate the array's flags to element access: a shared array's
                // elements are accessed with shared semantics (copy + share_op),
                // even though the runtime flags on the element may be Given.
                let element_flags = ObjectPerms::from_value_flags(env, &array_tv.ty, array_flags)?;
                let result =
                    self.give_object(env, elem_ptr, &element_ty, element_flags, "array_give")?;

                self.drop_value(env, &array_tv)?;
                Ok(Outcome::Value(result))
            }

            crate::grammar::Expr::ArrayDrop(parameters, array_expr, index_expr) => {
                let (_array_ty, element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.into_int_value(&index_tv)? as usize;
                let env = &stack_frame.env;
                self.drop_value(env, &index_tv)?;
                let element_size = self.size_of(env, &element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_drop")?;

                let elem_ptr = Pointer {
                    index: array_ptr.index,
                    offset: 2 + index * element_size,
                };

                // Check if element is uninitialized — dropping uninitialized is UB
                self.check_element_initialized(elem_ptr, "array_drop")?;

                // Propagate the array's flags to element drop, same as ArrayGive.
                let array_flags: ObjectPerms =
                    match self.read_flags(env, array_tv.pointer, &array_tv.ty)? {
                        Some(f) => f.into(),
                        None => ObjectPerms::Given,
                    };
                let flags = self.effective_flags(env, array_flags, elem_ptr, &element_ty)?;
                match flags {
                    ObjectPerms::Given | ObjectPerms::Shared => {
                        self.drop_value(env, elem_ptr, &element_ty)?;
                    }
                    ObjectPerms::Borrowed | ObjectPerms::MutRef => {} // no-op
                    ObjectPerms::Uninitialized => {
                        anyhow::bail!("array_drop: element is uninitialized")
                    }
                }

                self.free(env, &array_tv)?;
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Expr::ArraySet(parameters, array_expr, index_expr, value_expr) => {
                let (_array_ty, element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.read_int(&index_tv)? as usize;
                self.free(&stack_frame.env, &index_tv)?;
                let value_tv = self.eval_expr_value(stack_frame, value_expr)?;
                let env = &stack_frame.env;
                let element_size = self.size_of(env, &element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_set")?;

                let elem_ptr = Pointer {
                    index: array_ptr.index,
                    offset: 2 + index * element_size,
                };

                // Drop any existing value in the slot before writing the new one.
                if let Some(flags) = self.read_flags(env, elem_ptr, &element_ty)? {
                    match flags {
                        Flags::Given | Flags::Shared => {
                            self.drop_value(env, elem_ptr, &element_ty)?;
                        }
                        Flags::Borrowed | Flags::Uninitialized => {}
                    }
                }

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
    ) -> anyhow::Result<ObjectValue> {
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
        Word::MutRef(p) => {
            if p.offset == 0 {
                format!("MutRef(0x{:0>width$x})", p.index, width = hex_width)
            } else {
                format!(
                    "MutRef(0x{:0>width$x}+{})",
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

impl std::ops::Add<usize> for Pointer {
    type Output = Pointer;

    fn add(self, rhs: usize) -> Self::Output {
        Pointer {
            index: self.index,
            offset: self.offset + rhs,
        }
    }
}
