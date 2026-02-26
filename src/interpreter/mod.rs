use std::sync::Arc;

use formality_core::{Map, Upcast};

use crate::grammar::{
    ClassDecl, ClassDeclBoundData, FieldId, MethodDeclBoundData, MethodId, NamedTy, Parameter,
    ParameterPredicate, Program, Ty, TypeName, ValueId, Var,
};

use crate::type_system::env::Env;
use crate::type_system::predicates::MeetsPredicate;
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
    variables: Map<Var, TypedValue>,
}
// ANCHOR_END: StackFrame

// ANCHOR: Interpreter
pub struct Interpreter<'a> {
    program: &'a Program,
    env: Env,
    allocs: Vec<Alloc>,
    output: String,
}
// ANCHOR_END: Interpreter

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program) -> Self {
        let env = Env::new(Arc::new(program.clone()));
        Self {
            program,
            env,
            allocs: Vec::new(),
            output: String::new(),
        }
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
    /// e.g. `struct class Box[ty T]` has no flags when T is copy (Box[Int])
    /// but has flags when T is move (Box[Data]).
    fn has_flags(&self, ty: &Ty) -> HasFlags {
        let inner = ty.strip_perm();
        match &inner {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(_),
                ..
            }) => {
                if self.is_copy_type(&inner) {
                    HasFlags::No
                } else {
                    HasFlags::Yes
                }
            }
            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                ..
            }) => HasFlags::Yes,
            _ => HasFlags::No,
        }
    }

    /// Compute the word offset and type of a field within a class allocation.
    fn field_offset_by_name(
        &self,
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
        let mut offset = self.has_flags(&class_ty).to_usize();
        for field in &class_data.fields {
            if field.name == *field_id {
                return Ok((offset, field.ty.clone()));
            }
            offset += self.size_of(&field.ty)?;
        }
        anyhow::bail!("no field `{field_id:?}` in class `{class_name:?}`")
    }

    /// Determine if a parameter (type or permission) is copy.
    fn is_copy_parameter(&self, param: &Parameter) -> anyhow::Result<bool> {
        Ok(param.meets_predicate(&self.env, ParameterPredicate::Copy)?)
    }

    /// Check if a type is copy (delegates to the type system).
    fn is_copy_type(&self, ty: &Ty) -> bool {
        self.is_copy_parameter(&Parameter::Ty(ty.clone()))
            .unwrap_or(false)
    }

    /// Compute the size (in Words) of a type.
    fn size_of(&self, ty: &Ty) -> anyhow::Result<usize> {
        match ty {
            Ty::ApplyPerm(_, inner) => self.size_of(inner),
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
                        total += self.size_of(ty)?;
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

                    let mut total = self.has_flags(ty).to_usize();
                    for field in &fields {
                        total += self.size_of(&field.ty)?;
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
    fn copy_value(&mut self, ptr: Pointer, ty: &Ty) -> anyhow::Result<TypedValue> {
        let size = self.size_of(ty)?;
        let words = self.read_words(ptr, size);
        let new_ptr = self.alloc_raw(Alloc { data: words });
        Ok(TypedValue {
            pointer: new_ptr,
            ty: ty.clone(),
        })
    }

    /// Copy a value and overwrite its flags.
    fn copy_with_flag(&mut self, ptr: Pointer, ty: &Ty, flag: Flags) -> anyhow::Result<TypedValue> {
        let tv = self.copy_value(ptr, ty)?;
        if self.has_flags(ty) == HasFlags::Yes {
            self.write_flags(tv.pointer, ty, flag)?;
        }
        Ok(tv)
    }

    /// Mark a value as uninitialized.
    /// Sets the flags word to Flags::Uninitialized (if present) and
    /// overwrites all remaining data words with Word::Uninitialized.
    fn uninitialize(&mut self, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let flags_size = self.has_flags(ty).to_usize();
        if flags_size > 0 {
            self.write_word(ptr, Word::Flags(Flags::Uninitialized));
        }
        let size = self.size_of(ty)?;
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
    fn read_flags(&self, ptr: Pointer, ty: &Ty) -> anyhow::Result<Option<Flags>> {
        if self.has_flags(ty) == HasFlags::Yes {
            match self.read_word(ptr) {
                Word::Flags(f) => Ok(Some(f)),
                other => anyhow::bail!("expected Flags word, got {other:?}"),
            }
        } else {
            Ok(None)
        }
    }

    /// Write flags for a value.
    fn write_flags(&mut self, ptr: Pointer, ty: &Ty, flags: Flags) -> anyhow::Result<()> {
        anyhow::ensure!(
            self.has_flags(ty) == HasFlags::Yes,
            "write_flags on type without flags"
        );
        self.write_word(ptr, Word::Flags(flags));
        Ok(())
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
            Word::Int(n) => Ok(n),
            other => anyhow::bail!("expected Int refcount word, got {other:?}"),
        }
    }

    /// Write a new refcount to an array allocation (at offset 0).
    fn write_refcount(&mut self, array_alloc_ptr: Pointer, refcount: i64) {
        self.write_word(array_alloc_ptr, Word::Int(refcount));
    }

    /// Check that index is within array bounds.
    fn check_array_bounds(&self, array_ptr: Pointer, index: usize, op: &str) -> anyhow::Result<()> {
        let capacity = match self.read_word(Pointer {
            index: array_ptr.index,
            offset: 1,
        }) {
            Word::Int(n) => n as usize,
            other => anyhow::bail!("{op}: expected Int length word, got {other:?}"),
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
    /// Called by Expr::Share. Recursively flips flags Given→Shared.
    /// Does NOT increment array refcounts (no duplication occurs).
    fn convert_to_shared(&mut self, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let inner_ty = ty.strip_perm();
        match &inner_ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name)?;
                let class_data = class_decl.binder.instantiate_with(parameters)?;
                let has_flags = self.has_flags(&inner_ty);
                if has_flags == HasFlags::Yes {
                    match self.read_word(ptr) {
                        Word::Flags(Flags::Given) => {
                            self.write_word(ptr, Word::Flags(Flags::Shared));
                        }
                        // Borrowed or uninitialized: per spec, no-op — don't recurse.
                        Word::Flags(Flags::Borrowed) | Word::Flags(Flags::Uninitialized) => {
                            return Ok(());
                        }
                        _ => {}
                    }
                }
                let mut offset = has_flags.to_usize();
                for field in &class_data.fields {
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    self.convert_to_shared(field_ptr, &field.ty)?;
                    offset += self.size_of(&field.ty)?;
                }
                Ok(())
            }
            // Array: flip flags only, no refcount change (no duplication).
            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                ..
            }) => {
                if let Word::Flags(Flags::Given) = self.read_word(ptr) {
                    self.write_word(ptr, Word::Flags(Flags::Shared));
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Duplication accounting: called when a Shared value is copied
    /// (by place.give or place.ref on Shared). Increments array refcounts
    /// and recurses into class fields to account for nested duplications.
    fn share_op(&mut self, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let inner_ty = ty.strip_perm();
        match &inner_ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name)?;
                let class_data = class_decl.binder.instantiate_with(parameters)?;
                let mut offset = self.has_flags(&inner_ty).to_usize();
                for field in &class_data.fields {
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    self.share_op(field_ptr, &field.ty)?;
                    offset += self.size_of(&field.ty)?;
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
            _ => Ok(()),
        }
    }

    /// Drop a Given value: recursively drop Given fields, then uninitialize.
    fn drop_given(&mut self, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let inner_ty = ty.strip_perm();
        match &inner_ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name)?;
                let class_data = class_decl.binder.instantiate_with(parameters)?;
                let mut offset = self.has_flags(&inner_ty).to_usize();
                for field in &class_data.fields {
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    // Recursively drop fields that have flags
                    if let Some(field_flags) = self.read_flags(field_ptr, &field.ty)? {
                        match field_flags {
                            Flags::Given => self.drop_given(field_ptr, &field.ty)?,
                            Flags::Shared => self.drop_shared(field_ptr, &field.ty)?,
                            Flags::Borrowed | Flags::Uninitialized => {}
                        }
                    }
                    offset += self.size_of(&field.ty)?;
                }
                // Uninitialize this value
                self.uninitialize(ptr, &inner_ty)?;
                Ok(())
            }
            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                parameters,
            }) => {
                self.drop_array(ptr, parameters, &inner_ty)?;
                Ok(())
            }
            _ => {
                self.uninitialize(ptr, &inner_ty)?;
                Ok(())
            }
        }
    }

    /// Drop a Shared value: recursively apply drop-shared to fields,
    /// then uninitialize.
    fn drop_shared(&mut self, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        let inner_ty = ty.strip_perm();
        match &inner_ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(class_name),
                parameters,
            }) => {
                let class_decl = self.program.class_named(class_name)?;
                let class_data = class_decl.binder.instantiate_with(parameters)?;
                let mut offset = self.has_flags(&inner_ty).to_usize();
                for field in &class_data.fields {
                    let field_ptr = Pointer {
                        index: ptr.index,
                        offset: ptr.offset + offset,
                    };
                    // For give|share class fields, recurse
                    if let Some(field_flags) = self.read_flags(field_ptr, &field.ty)? {
                        match field_flags {
                            Flags::Given | Flags::Shared => {
                                self.drop_shared(field_ptr, &field.ty)?;
                            }
                            Flags::Borrowed | Flags::Uninitialized => {}
                        }
                    }
                    offset += self.size_of(&field.ty)?;
                }
                // Uninitialize this value
                self.uninitialize(ptr, &inner_ty)?;
                Ok(())
            }
            Ty::NamedTy(NamedTy {
                name: TypeName::Array,
                parameters,
            }) => {
                self.drop_array(ptr, parameters, &inner_ty)?;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Drop an array reference: decrement refcount, and if it reaches zero,
    /// recursively drop all initialized elements and free the allocation.
    /// Then uninitialize the value (the two-word [Flags, Pointer] representation).
    fn drop_array(
        &mut self,
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
                Word::Int(n) => n as usize,
                other => anyhow::bail!("drop_array: expected Int length word, got {other:?}"),
            };
            let element_size = self.size_of(&element_ty)?;
            for i in 0..capacity {
                let elem_ptr = Pointer {
                    index: array_alloc_ptr.index,
                    offset: 2 + i * element_size,
                };
                // Dispatch drop based on element flags (skip uninitialized)
                if let Some(flags) = self.read_flags(elem_ptr, &element_ty)? {
                    match flags {
                        Flags::Given => self.drop_given(elem_ptr, &element_ty)?,
                        Flags::Shared => self.drop_shared(elem_ptr, &element_ty)?,
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
        self.uninitialize(ptr, inner_ty)?;
        Ok(())
    }

    /// Free a TypedValue: drop its content, then overwrite ALL words with
    /// Word::Uninitialized. The allocation becomes dead memory — any subsequent
    /// access is a fault.
    ///
    /// This is the uniform cleanup operation for temporaries: every expression
    /// evaluation yields a fresh allocation, and consumers free it when done.
    fn free(&mut self, tv: &TypedValue) -> anyhow::Result<()> {
        // Step 1: Drop content (recurse into flagged fields, decrement refcounts)
        if let Some(flags) = self.read_flags(tv.pointer, &tv.ty)? {
            match flags {
                Flags::Given => self.drop_given(tv.pointer, &tv.ty)?,
                Flags::Shared => self.drop_shared(tv.pointer, &tv.ty)?,
                Flags::Borrowed | Flags::Uninitialized => {}
            }
        }
        // Step 2: Overwrite ALL words with Uninitialized (including flags)
        let size = self.size_of(&tv.ty.strip_perm())?;
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

    /// Resolve a grammar Place to a pointer and type.
    fn resolve_place(
        &self,
        stack_frame: &StackFrame,
        place: &crate::grammar::Place,
    ) -> anyhow::Result<(Pointer, Ty)> {
        let tv = stack_frame
            .variables
            .get(&place.var)
            .ok_or_else(|| anyhow::anyhow!("undefined variable `{:?}`", place.var))?;

        let mut current_ptr = tv.pointer;
        let mut current_ty = tv.ty.clone();

        for projection in &place.projections {
            match projection {
                crate::grammar::Projection::Field(field_id) => {
                    // Check flags before projecting through a class value.
                    // Per the spec, accessing through an Uninitialized value is UB.
                    if let Some(Flags::Uninitialized) = self.read_flags(current_ptr, &current_ty)? {
                        anyhow::bail!(
                            "access through uninitialized value: `{:?}.{:?}`",
                            place.var,
                            field_id
                        );
                    }

                    let inner_ty = current_ty.strip_perm();
                    match &inner_ty {
                        Ty::NamedTy(NamedTy {
                            name: TypeName::Id(class_name),
                            parameters,
                        }) => {
                            let (field_offset, field_ty) =
                                self.field_offset_by_name(class_name, parameters, field_id)?;
                            current_ptr = Pointer {
                                index: current_ptr.index,
                                offset: current_ptr.offset + field_offset,
                            };
                            current_ty = field_ty;
                        }
                        _ => anyhow::bail!("field access on non-class type: {current_ty:?}"),
                    }
                }
            }
        }

        Ok((current_ptr, current_ty))
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
    pub fn display_value(&self, tv: &TypedValue) -> String {
        let mut buf = String::new();
        self.fmt_value(&mut buf, tv.pointer, &tv.ty);
        buf
    }

    fn fmt_value(&self, buf: &mut String, ptr: Pointer, ty: &Ty) {
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
                let has_flags = self.has_flags(&inner_ty) == HasFlags::Yes;

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
                    self.fmt_value(buf, field_ptr, &field.ty);
                    offset += self.size_of(&field.ty).unwrap();
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
                let Word::Int(capacity) = self.read_word(Pointer {
                    index: array_ptr.index,
                    offset: 1,
                }) else {
                    write!(buf, ", <bad capacity> }}").unwrap();
                    return;
                };
                let element_size = self.size_of(&element_ty).unwrap();
                for i in 0..capacity as usize {
                    write!(buf, ", ").unwrap();
                    let elem_ptr = Pointer {
                        index: array_ptr.index,
                        offset: 2 + i * element_size,
                    };
                    self.fmt_value(buf, elem_ptr, &element_ty);
                }
                write!(buf, " }}").unwrap();
            }

            _ => match self.read_word(ptr) {
                Word::Uninitialized => write!(buf, "uninitialized").unwrap(),
                Word::Pointer(p) => write!(buf, "<ptr:{p:?}>").unwrap(),
                other => write!(buf, "{other:?}").unwrap(),
            },
        }
    }

    // ---------------------------------------------------------------
    // Instantiation
    // ---------------------------------------------------------------

    fn instantiate_class(
        &mut self,
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
        let has_flags = self.has_flags(&class_ty) == HasFlags::Yes;
        if has_flags {
            data.push(Word::Flags(Flags::Given));
        }

        // Copy field words into the allocation
        for (field_decl, field_tv) in fields.iter().zip(field_values) {
            let field_size = self.size_of(&field_decl.ty)?;
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
            this: _this_decl,
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

        // Create stack frame populated with typed variables
        let mut stack_frame = StackFrame {
            variables: Default::default(),
        };
        stack_frame.variables.insert(Var::This, this);
        for (input, input_value) in inputs.iter().zip(input_values) {
            stack_frame
                .variables
                .insert(Var::Id(input.name.clone()), input_value);
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
                let vars: Vec<TypedValue> = stack_frame
                    .variables
                    .into_values()
                    .collect();
                for tv in vars {
                    self.free(&tv)?;
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
        let object = self.instantiate_class(&main_class, &[], &[])?;
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
                    self.free(&final_value)?;
                    final_value = tv;
                }
                early @ (Outcome::Break | Outcome::Return(_)) => {
                    self.free(&final_value)?;
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
                stack_frame
                    .variables
                    .insert(Var::Id(name.clone()), tv);
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Statement::Reassign(place, expr) => {
                let tv = self.eval_expr_value(stack_frame, expr)?;
                let (target_ptr, target_ty) = self.resolve_place(stack_frame, place)?;
                // Drop the old value at the target before overwriting it.
                let old_tv = TypedValue {
                    pointer: target_ptr,
                    ty: target_ty.clone(),
                };
                self.free(&old_tv)?;
                // Bitwise copy: ownership moves into the target.
                let size = self.size_of(&target_ty)?;
                let words = self.read_words(tv.pointer, size);
                self.write_words(target_ptr, &words);
                // Scrub the temp without dropping — ownership was transferred.
                self.uninitialize(tv.pointer, &tv.ty)?;
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Statement::Loop(body) => loop {
                match self.eval_expr(stack_frame, body)? {
                    Outcome::Value(tv) => {
                        self.free(&tv)?;
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
                let text = self.display_value(&tv);
                self.free(&tv)?;
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
                self.free(&l)?;
                self.free(&r)?;
                Ok(Outcome::Value(TypedValue {
                    pointer: self.alloc_int(a + b),
                    ty: Ty::int(),
                }))
            }

            crate::grammar::Expr::Block(block) => self.eval_block(stack_frame, block),

            crate::grammar::Expr::Tuple(exprs) => {
                for expr in exprs {
                    let tv = self.eval_expr_value(stack_frame, expr)?;
                    self.free(&tv)?;
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
                let result = self.instantiate_class(
                    class_name,
                    params,
                    &field_values,
                )?;
                for fv in &field_values {
                    // Scrub the temp without dropping — ownership moved into the class.
                    self.uninitialize(fv.pointer, &fv.ty)?;
                }
                Ok(Outcome::Value(result))
            }

            crate::grammar::Expr::Place(crate::grammar::PlaceExpr { place, access }) => {
                let (ptr, ty) = self.resolve_place(stack_frame, place)?;
                let flags = self.read_flags(ptr, &ty)?;
                let tv = match access {
                    crate::grammar::Access::Gv => match flags {
                        Some(Flags::Given) => {
                            let copied = self.copy_value(ptr, &ty)?;
                            self.uninitialize(ptr, &ty)?;
                            copied
                        }
                        Some(Flags::Shared) => {
                            let copied = self.copy_with_flag(ptr, &ty, Flags::Shared)?;
                            self.share_op(copied.pointer, &ty)?;
                            copied
                        }
                        Some(Flags::Borrowed) => self.copy_with_flag(ptr, &ty, Flags::Borrowed)?,
                        Some(Flags::Uninitialized) => {
                            anyhow::bail!("give of uninitialized value")
                        }
                        None => self.copy_value(ptr, &ty)?,
                    },
                    crate::grammar::Access::Rf => match flags {
                        Some(Flags::Shared) => {
                            let copied = self.copy_with_flag(ptr, &ty, Flags::Shared)?;
                            self.share_op(copied.pointer, &ty)?;
                            copied
                        }
                        Some(Flags::Given) | Some(Flags::Borrowed) => {
                            self.copy_with_flag(ptr, &ty, Flags::Borrowed)?
                        }
                        Some(Flags::Uninitialized) => {
                            anyhow::bail!("ref of uninitialized value")
                        }
                        None => self.copy_value(ptr, &ty)?,
                    },
                    crate::grammar::Access::Mt => {
                        anyhow::bail!("mut access not yet implemented")
                    }
                    crate::grammar::Access::Drop => {
                        match flags {
                            Some(Flags::Given) => {
                                self.drop_given(ptr, &ty)?;
                            }
                            Some(Flags::Shared) => {
                                self.drop_shared(ptr, &ty)?;
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
                let flags = self.read_flags(tv.pointer, &tv.ty)?;
                match flags {
                    Some(Flags::Given) => {
                        self.write_flags(tv.pointer, &tv.ty, Flags::Shared)?;
                        self.convert_to_shared(tv.pointer, &tv.ty)?;
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
                self.free(&cond_tv)?;
                if n != 0 {
                    self.eval_expr(stack_frame, if_true)
                } else {
                    self.eval_expr(stack_frame, if_false)
                }
            }

            crate::grammar::Expr::SizeOf(parameters) => {
                let ty = extract_size_of_ty(parameters)?;
                let size = self.size_of(&ty)?;
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
                self.free(&length_tv)?;
                anyhow::ensure!(length >= 0, "array_new: negative length {length}");
                let length = length as usize;
                let element_size = self.size_of(&element_ty)?;

                // Allocate: [Int(refcount), Int(length), element_slots...]
                // Each element slot has Flags::Uninitialized if the element type has flags,
                // otherwise Word::Uninitialized for all words.
                let has_flags = self.has_flags(&element_ty) == HasFlags::Yes;
                let mut data = vec![Word::Int(1), Word::Int(length as i64)];
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
                self.free(&array_tv)?;
                match capacity {
                    Word::Int(n) => Ok(Outcome::Value(TypedValue {
                        pointer: self.alloc_int(n),
                        ty: Ty::int(),
                    })),
                    other => {
                        anyhow::bail!("array_capacity: expected Int length word, got {other:?}")
                    }
                }
            }

            crate::grammar::Expr::ArrayGet(parameters, array_expr, index_expr) => {
                let (_array_ty, element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.expect_int(&index_tv)? as usize;
                self.free(&index_tv)?;
                let element_size = self.size_of(&element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_get")?;

                let elem_ptr = Pointer {
                    index: array_ptr.index,
                    offset: 2 + index * element_size,
                };

                // Check if element is uninitialized
                self.check_element_initialized(elem_ptr, "array_get")?;

                // Copy element out (move semantics)
                let result = self.copy_value(elem_ptr, &element_ty)?;

                // Mark source slot as uninitialized (move out)
                self.uninitialize(elem_ptr, &element_ty)?;

                self.free(&array_tv)?;
                Ok(Outcome::Value(result))
            }

            crate::grammar::Expr::ArrayDrop(parameters, array_expr, index_expr) => {
                let (_array_ty, element_ty) = extract_array_ty(parameters)?;
                let array_tv = self.eval_expr_value(stack_frame, array_expr)?;
                let array_ptr = self.expect_array_ptr(&array_tv)?;
                let index_tv = self.eval_expr_value(stack_frame, index_expr)?;
                let index = self.expect_int(&index_tv)? as usize;
                self.free(&index_tv)?;
                let element_size = self.size_of(&element_ty)?;
                self.check_array_bounds(array_ptr, index, "array_drop")?;

                let elem_ptr = Pointer {
                    index: array_ptr.index,
                    offset: 2 + index * element_size,
                };

                // Check if element is uninitialized — dropping uninitialized is UB
                self.check_element_initialized(elem_ptr, "array_drop")?;

                // Dispatch drop based on element flags
                if let Some(flags) = self.read_flags(elem_ptr, &element_ty)? {
                    match flags {
                        Flags::Given => self.drop_given(elem_ptr, &element_ty)?,
                        Flags::Shared => self.drop_shared(elem_ptr, &element_ty)?,
                        Flags::Borrowed => {} // no-op
                        Flags::Uninitialized => {
                            anyhow::bail!("array_drop: element is uninitialized")
                        }
                    }
                } else {
                    // No flags (e.g., Int) — just uninitialize
                    self.uninitialize(elem_ptr, &element_ty)?;
                }

                self.free(&array_tv)?;
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
                self.free(&index_tv)?;
                let value_tv = self.eval_expr_value(stack_frame, value_expr)?;
                let element_size = self.size_of(&element_ty)?;
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
                self.uninitialize(value_tv.pointer, &value_tv.ty)?;
                self.free(&value_tv)?;

                self.free(&array_tv)?;
                Ok(Outcome::Value(self.unit_value()))
            }

            crate::grammar::Expr::Panic => anyhow::bail!("panic!"),

            crate::grammar::Expr::Clear(var) => {
                if let Some(tv) = stack_frame.variables.get(&Var::Id(var.clone())) {
                    let tv = tv.clone();
                    self.uninitialize(tv.pointer, &tv.ty)?;
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
