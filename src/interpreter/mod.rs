use std::sync::Arc;

use formality_core::{Map, Upcast};

use crate::grammar::{
    ClassDecl, ClassDeclBoundData, FieldId, MethodDeclBoundData, MethodId,
    NamedTy, Parameter, ParameterPredicate, Program, Ty, TypeName, ValueId, Var,
};

use crate::type_system::env::Env;
use crate::type_system::predicates::MeetsPredicate;
use std::fmt::Write;

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

    /// Allocate a single `Uninitialized` word (used for unit values).
    fn alloc_uninitialized(&mut self) -> Pointer {
        self.alloc_raw(Alloc {
            data: vec![Word::Uninitialized],
        })
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
    fn type_has_flags(&self, ty: &Ty) -> anyhow::Result<bool> {
        let inner = ty.strip_perm();
        match &inner {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(_),
                ..
            }) => Ok(!self.is_copy_type(&inner)),
            _ => Ok(false),
        }
    }

    /// Returns 1 if this class instantiated with these parameters needs a flags word, 0 otherwise.
    fn named_ty_flags_size(&self, name: &TypeName, parameters: &[Parameter]) -> usize {
        let ty = Ty::NamedTy(NamedTy {
            name: name.clone(),
            parameters: parameters.to_vec(),
        });
        if self.type_has_flags(&ty).unwrap_or(false) {
            1
        } else {
            0
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
        let mut offset = self.named_ty_flags_size(&class_name.upcast(), parameters);
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

                    let flags_size = self.named_ty_flags_size(name, parameters);

                    let mut field_size = 0;
                    for field in &fields {
                        field_size += self.size_of(&field.ty)?;
                    }

                    Ok(flags_size + field_size)
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

    /// Copy a value and overwrite its flags word.
    fn copy_with_flag(
        &mut self,
        ptr: Pointer,
        ty: &Ty,
        flag: Flags,
    ) -> anyhow::Result<TypedValue> {
        let tv = self.copy_value(ptr, ty)?;
        if self.type_has_flags(ty)? {
            self.write_word(tv.pointer, Word::Flags(flag));
        }
        Ok(tv)
    }

    /// Mark a value as uninitialized.
    fn uninitialize(&mut self, ptr: Pointer, ty: &Ty) -> anyhow::Result<()> {
        if self.type_has_flags(ty)? {
            // For unique classes, just set the flags word
            self.write_word(ptr, Word::Flags(Flags::Uninitialized));
        } else {
            // For ints, shared classes, etc: overwrite all words
            let size = self.size_of(ty)?;
            for i in 0..size {
                self.write_word(
                    Pointer {
                        index: ptr.index,
                        offset: ptr.offset + i,
                    },
                    Word::Uninitialized,
                );
            }
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
                let has_flags = self.type_has_flags(&inner_ty).unwrap_or(false);

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

            _ => match self.read_word(ptr) {
                Word::Uninitialized => write!(buf, "uninitialized").unwrap(),
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
        let has_flags = self.named_ty_flags_size(&class_name.upcast(), parameters) > 0;
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
            crate::grammar::MethodBody::Block(block) => self.eval_block(&mut stack_frame, block),
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
    ) -> anyhow::Result<TypedValue> {
        let crate::grammar::Block { statements } = block;

        let mut final_value = TypedValue {
            pointer: self.alloc_uninitialized(),
            ty: Ty::unit(),
        };
        for statement in statements {
            final_value = self.eval_statement(stack_frame, statement)?;
        }
        Ok(final_value)
    }

    fn eval_statement(
        &mut self,
        stack_frame: &mut StackFrame,
        statement: &crate::grammar::Statement,
    ) -> anyhow::Result<TypedValue> {
        match statement {
            crate::grammar::Statement::Expr(expr) => self.eval_expr(stack_frame, expr),

            crate::grammar::Statement::Let(name, _ascription, expr) => {
                let tv = self.eval_expr(stack_frame, expr)?;
                stack_frame
                    .variables
                    .insert(Var::Id(name.clone()), tv.clone());
                Ok(tv)
            }

            crate::grammar::Statement::Reassign(place, expr) => {
                let tv = self.eval_expr(stack_frame, expr)?;
                let (target_ptr, target_ty) = self.resolve_place(stack_frame, place)?;
                let size = self.size_of(&target_ty)?;
                let words = self.read_words(tv.pointer, size);
                self.write_words(target_ptr, &words);
                Ok(TypedValue {
                    pointer: self.alloc_uninitialized(),
                    ty: Ty::unit(),
                })
            }

            crate::grammar::Statement::Loop(body) => loop {
                match self.eval_expr(stack_frame, body) {
                    Ok(_) => continue,
                    Err(e) => {
                        // TODO: catch Break specifically
                        return Err(e);
                    }
                }
            },

            crate::grammar::Statement::Break => {
                // TODO: need a control flow mechanism for break
                anyhow::bail!("break")
            }

            crate::grammar::Statement::Return(expr) => {
                let _tv = self.eval_expr(stack_frame, expr)?;
                // TODO: need a control flow mechanism for return
                anyhow::bail!("return")
            }

            crate::grammar::Statement::Print(expr) => {
                let tv = self.eval_expr(stack_frame, expr)?;
                let text = self.display_value(&tv);
                self.output.push_str(&text);
                self.output.push('\n');
                Ok(TypedValue {
                    pointer: self.alloc_uninitialized(),
                    ty: Ty::unit(),
                })
            }
        }
    }

    fn eval_expr(
        &mut self,
        stack_frame: &mut StackFrame,
        expr: &crate::grammar::Expr,
    ) -> anyhow::Result<TypedValue> {
        match expr {
            crate::grammar::Expr::Integer(n) => Ok(TypedValue {
                pointer: self.alloc_int(*n as i64),
                ty: Ty::int(),
            }),

            crate::grammar::Expr::Add(lhs, rhs) => {
                let l = self.eval_expr(stack_frame, lhs)?;
                let r = self.eval_expr(stack_frame, rhs)?;
                let a = self.expect_int(&l)?;
                let b = self.expect_int(&r)?;
                Ok(TypedValue {
                    pointer: self.alloc_int(a + b),
                    ty: Ty::int(),
                })
            }

            crate::grammar::Expr::Block(block) => self.eval_block(stack_frame, block),

            crate::grammar::Expr::Tuple(exprs) => {
                for expr in exprs {
                    self.eval_expr(stack_frame, expr)?;
                }
                Ok(TypedValue {
                    pointer: self.alloc_raw(Alloc { data: vec![] }),
                    ty: Ty::unit(),
                })
            }

            crate::grammar::Expr::New(class_name, params, field_exprs) => {
                let field_values: Vec<TypedValue> = field_exprs
                    .iter()
                    .map(|e| self.eval_expr(stack_frame, e))
                    .collect::<Result<_, _>>()?;
                self.instantiate_class(class_name, params, &field_values)
            }

            crate::grammar::Expr::Place(crate::grammar::PlaceExpr { place, access }) => {
                let (ptr, ty) = self.resolve_place(stack_frame, place)?;
                match access {
                    crate::grammar::Access::Gv => {
                        let copied = self.copy_value(ptr, &ty)?;
                        if !self.is_copy_type(&ty) {
                            self.uninitialize(ptr, &ty)?;
                        }
                        Ok(copied)
                    }
                    crate::grammar::Access::Rf => self.copy_with_flag(ptr, &ty, Flags::Borrowed),
                    crate::grammar::Access::Mt => {
                        anyhow::bail!("mut access not yet implemented")
                    }
                    crate::grammar::Access::Sh => self.copy_with_flag(ptr, &ty, Flags::Shared),
                    crate::grammar::Access::Drop => {
                        if !self.is_copy_type(&ty) {
                            self.uninitialize(ptr, &ty)?;
                        }
                        Ok(TypedValue {
                            pointer: self.alloc_uninitialized(),
                            ty: Ty::unit(),
                        })
                    }
                }
            }

            crate::grammar::Expr::Share(expr) => {
                let tv = self.eval_expr(stack_frame, expr)?;
                if self.type_has_flags(&tv.ty)? {
                    self.write_word(tv.pointer, Word::Flags(Flags::Shared));
                }
                Ok(tv)
            }

            crate::grammar::Expr::Call(receiver, method_name, method_params, args) => {
                let receiver_tv = self.eval_expr(stack_frame, receiver)?;
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
                    .map(|a| self.eval_expr(stack_frame, a))
                    .collect::<Result<_, _>>()?;
                self.call_method(
                    &class_name,
                    &class_parameters,
                    method_name,
                    method_params,
                    receiver_tv,
                    arg_vals,
                )
            }

            crate::grammar::Expr::If(cond, if_true, if_false) => {
                let cond_tv = self.eval_expr(stack_frame, cond)?;
                let n = self.expect_int(&cond_tv)?;
                if n != 0 {
                    self.eval_expr(stack_frame, if_true)
                } else {
                    self.eval_expr(stack_frame, if_false)
                }
            }

            crate::grammar::Expr::SizeOf(parameters) => {
                let ty = extract_size_of_ty(parameters)?;
                let size = self.size_of(&ty)?;
                Ok(TypedValue {
                    pointer: self.alloc_int(size as i64),
                    ty: Ty::int(),
                })
            }

            crate::grammar::Expr::Panic => anyhow::bail!("panic!"),

            crate::grammar::Expr::Clear(var) => {
                if let Some(tv) = stack_frame.variables.get(&Var::Id(var.clone())) {
                    let tv = tv.clone();
                    self.uninitialize(tv.pointer, &tv.ty)?;
                }
                Ok(TypedValue {
                    pointer: self.alloc_uninitialized(),
                    ty: Ty::unit(),
                })
            }
        }
    }
}

fn extract_size_of_ty(parameters: &[Parameter]) -> anyhow::Result<Ty> {
    match parameters {
        [Parameter::Ty(ty)] => Ok(ty.clone()),
        _ => anyhow::bail!("size_of requires exactly one type parameter"),
    }
}
