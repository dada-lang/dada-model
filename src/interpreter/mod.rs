use std::sync::Arc;

use formality_core::{Map, Upcast};

use crate::grammar::{
    ClassDecl, ClassDeclBoundData, ClassPredicate, FieldId, MethodDeclBoundData,
    MethodId, Parameter, ParameterPredicate, Program, TypeName, ValueId, Var,
};

use crate::type_system::env::Env;
use crate::type_system::predicates::MeetsPredicate;
use std::fmt::Write;

#[cfg(test)]
mod tests;

// ANCHOR: Value
/// Index into the `Interpreter::values` array.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Value(usize);
// ANCHOR_END: Value

// ANCHOR: ValueData
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ValueData {
    Int(i64),
    Pointer(Value),
    Object(ObjectData),
    Uninitialized,
}
// ANCHOR_END: ValueData

// ANCHOR: ObjectData
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ObjectData {
    flag: ObjectFlag,
    class: TypeName,
    parameters: Vec<Parameter>,
    fields: Map<FieldId, Value>,
}
// ANCHOR_END: ObjectData

// ANCHOR: ObjectFlag
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ObjectFlag {
    Owned,
    Shared,
    Ref,
}
// ANCHOR_END: ObjectFlag

// ANCHOR: StackFrame
pub struct StackFrame {
    variables: Map<Var, Value>,
}
// ANCHOR_END: StackFrame

// ANCHOR: Interpreter
pub struct Interpreter<'a> {
    program: &'a Program,
    env: Env,
    values: Vec<ValueData>,
}
// ANCHOR_END: Interpreter

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program) -> Self {
        let env = Env::new(Arc::new(program.clone()));
        Self {
            program,
            env,
            values: Vec::new(),
        }
    }

    /// Allocate a new value slot and return its index.
    fn alloc(&mut self, data: ValueData) -> Value {
        let index = self.values.len();
        self.values.push(data);
        Value(index)
    }

    /// Read the data at a value slot.
    fn read(&self, value: Value) -> &ValueData {
        &self.values[value.0]
    }

    /// Write data into a value slot.
    fn write(&mut self, value: Value, data: ValueData) {
        self.values[value.0] = data;
    }

    /// Copy a value into a new slot, recursively copying object fields
    /// but stopping at pointer indirection.
    fn copy(&mut self, value: Value) -> Value {
        let data = self.read(value).clone();
        match data {
            ValueData::Int(_) | ValueData::Uninitialized => self.alloc(data),
            ValueData::Pointer(target) => self.alloc(ValueData::Pointer(target)),
            ValueData::Object(obj) => {
                let new_fields: Map<FieldId, Value> = obj
                    .fields
                    .iter()
                    .map(|(name, &field_val)| (name.clone(), self.copy(field_val)))
                    .collect();
                self.alloc(ValueData::Object(ObjectData {
                    flag: obj.flag,
                    class: obj.class,
                    parameters: obj.parameters,
                    fields: new_fields,
                }))
            }
        }
    }

    /// Copy a value, changing the top-level object flag.
    fn copy_with_flag(&mut self, value: Value, flag: ObjectFlag) -> Value {
        let copied = self.copy(value);
        match &mut self.values[copied.0] {
            ValueData::Object(obj) => obj.flag = flag,
            _ => {} // non-objects don't have flags
        }
        copied
    }

    /// Resolve a grammar Place to the Value slot it refers to.
    fn resolve_place(
        &self,
        stack_frame: &StackFrame,
        place: &crate::grammar::Place,
    ) -> anyhow::Result<Value> {
        let var_value = stack_frame
            .variables
            .get(&place.var)
            .ok_or_else(|| anyhow::anyhow!("undefined variable `{:?}`", place.var))?;

        let mut current = *var_value;
        for projection in &place.projections {
            match projection {
                crate::grammar::Projection::Field(field_id) => {
                    // Follow pointers transparently
                    current = self.deref(current);
                    match self.read(current) {
                        ValueData::Object(obj) => {
                            current = *obj
                                .fields
                                .get(field_id)
                                .ok_or_else(|| anyhow::anyhow!("no field `{:?}`", field_id))?;
                        }
                        _ => anyhow::bail!("field access on non-object"),
                    }
                }
            }
        }

        Ok(current)
    }

    /// Follow Pointer indirection to get the underlying slot.
    fn deref(&self, value: Value) -> Value {
        match self.read(value) {
            ValueData::Pointer(target) => self.deref(*target),
            _ => value,
        }
    }

    /// Determine if a parameter (type or permission) is copy.
    /// Delegates to the type system's MeetsPredicate trait.
    fn is_copy_parameter(&self, param: &Parameter) -> anyhow::Result<bool> {
        Ok(param.meets_predicate(&self.env, ParameterPredicate::Copy)?)
    }

    /// Check if a value is copy at runtime.
    /// Ints are always copy. Objects are copy if their flag is Shared.
    /// Pointers and Uninitialized are not copy.
    fn is_copy_value(&self, value: Value) -> bool {
        match self.read(value) {
            ValueData::Int(_) => true,
            ValueData::Object(obj) => obj.flag == ObjectFlag::Shared,
            ValueData::Pointer(_) | ValueData::Uninitialized => false,
        }
    }

    /// Pretty-print a value for display.
    pub fn display_value(&self, value: Value) -> String {
        let mut buf = String::new();
        self.fmt_value(&mut buf, value);
        buf
    }

    fn fmt_value(&self, buf: &mut String, value: Value) {
        match self.read(value) {
            ValueData::Int(n) => write!(buf, "{n}").unwrap(),
            ValueData::Pointer(target) => self.fmt_value(buf, *target),
            ValueData::Uninitialized => write!(buf, "uninitialized").unwrap(),
            ValueData::Object(obj) => {
                let name = match &obj.class {
                    TypeName::Id(id) => format!("{id:?}"),
                    TypeName::Int => "Int".to_string(),
                    TypeName::Tuple(n) => format!("Tuple({n})"),
                };
                write!(buf, "{name}").unwrap();
                write!(buf, " {{ ").unwrap();
                write!(buf, "flag: {:?}", obj.flag).unwrap();
                for (field, &val) in &obj.fields {
                    write!(buf, ", {field:?}: ").unwrap();
                    self.fmt_value(buf, val);
                }
                write!(buf, " }}").unwrap();
            }
        }
    }

    /// Run a program by instantiating `Main()` and calling `main`.
    pub fn interpret(&mut self) -> anyhow::Result<Value> {
        let main_class: ValueId = crate::dada_lang::try_term("Main")?;
        let main_method: MethodId = crate::dada_lang::try_term("main")?;
        let object = self.instantiate_class(&main_class, &[], &[])?;
        self.call_method(&main_class, &[], &main_method, &[], object, vec![])
    }

    fn instantiate_class(
        &mut self,
        class_name: &ValueId,
        parameters: &[Parameter],
        field_values: &[Value],
    ) -> anyhow::Result<Value> {
        let ClassDecl {
            name: _,
            class_predicate,
            binder,
        } = self.program.class_named(&class_name)?;

        let ClassDeclBoundData {
            predicates: _,
            fields,
            methods: _,
        } = binder.instantiate_with(parameters)?;

        if fields.len() != field_values.len() {
            anyhow::bail!(
                "class `{:?}` has {} fields but {} were provided",
                class_name,
                fields.len(),
                field_values.len()
            );
        }

        let field_map = fields
            .iter()
            .zip(field_values)
            .map(|(field_decl, value)| (field_decl.name.clone(), *value))
            .collect();

        let all_params_copy = parameters
            .iter()
            .all(|p| self.is_copy_parameter(p).unwrap_or(false));

        let flag = match class_predicate {
            ClassPredicate::Guard => ObjectFlag::Owned,
            ClassPredicate::Share => ObjectFlag::Owned,
            ClassPredicate::Shared => {
                if all_params_copy {
                    ObjectFlag::Shared
                } else {
                    ObjectFlag::Owned
                }
            }
        };

        Ok(self.alloc(ValueData::Object(ObjectData {
            flag,
            class: class_name.upcast(),
            parameters: parameters.to_vec(),
            fields: field_map,
        })))
    }

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
        } = self.program.class_named(&class_name)?;

        let ClassDeclBoundData {
            predicates: _,
            fields: _,
            methods,
        } = binder.instantiate_with(class_parameters)?;

        let method_decl = methods
            .iter()
            .find(|m| m.name == *method_id)
            .ok_or_else(|| {
                anyhow::anyhow!("class `{:?}` has no method `{:?}`", class_name, method_id)
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
        this: Value,
        input_values: Vec<Value>,
    ) -> anyhow::Result<Value> {
        let MethodDeclBoundData {
            this: _,
            inputs,
            output: _,
            predicates: _,
            body,
        } = self.find_method(class_name, class_parameters, method_id, method_parameters)?;

        if inputs.len() != input_values.len() {
            anyhow::bail!(
                "method `{:?}` of class `{:?}` has {} parameters but {} were provided",
                method_id,
                class_name,
                inputs.len(),
                input_values.len()
            );
        }

        // Create stack frame populated with variables
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
                "method `{:?}` of class `{:?}` is trusted and cannot be called by the interpreter",
                method_id,
                class_name
            ),
            crate::grammar::MethodBody::Block(block) => self.eval_block(&mut stack_frame, block),
        }
    }

    fn eval_block(
        &mut self,
        stack_frame: &mut StackFrame,
        block: &crate::grammar::Block,
    ) -> anyhow::Result<Value> {
        let crate::grammar::Block { statements } = block;

        let mut final_value = self.alloc(ValueData::Uninitialized);
        for statement in statements {
            final_value = self.eval_statement(stack_frame, statement)?;
        }
        Ok(final_value)
    }

    fn eval_statement(
        &mut self,
        stack_frame: &mut StackFrame,
        statement: &crate::grammar::Statement,
    ) -> anyhow::Result<Value> {
        match statement {
            crate::grammar::Statement::Expr(expr) => self.eval_expr(stack_frame, expr),
            crate::grammar::Statement::Let(name, _ascription, expr) => {
                let value = self.eval_expr(stack_frame, expr)?;
                stack_frame.variables.insert(Var::Id(name.clone()), value);
                self.alloc(ValueData::Uninitialized);
                Ok(value)
            }
            crate::grammar::Statement::Reassign(place, expr) => {
                let value = self.eval_expr(stack_frame, expr)?;
                let target = self.resolve_place(stack_frame, place)?;
                // Copy the data from value's slot into target's slot
                let data = self.read(value).clone();
                self.write(target, data);
                Ok(self.alloc(ValueData::Uninitialized))
            }
            crate::grammar::Statement::Loop(body) => {
                loop {
                    match self.eval_expr(stack_frame, body) {
                        Ok(_) => continue,
                        Err(e) => {
                            // TODO: catch Break specifically
                            return Err(e);
                        }
                    }
                }
            }
            crate::grammar::Statement::Break => {
                // TODO: need a control flow mechanism for break
                anyhow::bail!("break")
            }
            crate::grammar::Statement::Return(expr) => {
                let _value = self.eval_expr(stack_frame, expr)?;
                // TODO: need a control flow mechanism for return
                anyhow::bail!("return")
            }
        }
    }

    fn eval_expr(
        &mut self,
        stack_frame: &mut StackFrame,
        expr: &crate::grammar::Expr,
    ) -> anyhow::Result<Value> {
        match expr {
            crate::grammar::Expr::Integer(n) => Ok(self.alloc(ValueData::Int(*n as i64))),

            crate::grammar::Expr::Add(lhs, rhs) => {
                let l = self.eval_expr(stack_frame, lhs)?;
                let r = self.eval_expr(stack_frame, rhs)?;
                match (self.read(l), self.read(r)) {
                    (ValueData::Int(a), ValueData::Int(b)) => {
                        let result = a + b;
                        Ok(self.alloc(ValueData::Int(result)))
                    }
                    _ => anyhow::bail!("add requires two integers"),
                }
            }

            crate::grammar::Expr::Block(block) => self.eval_block(stack_frame, block),

            crate::grammar::Expr::Tuple(exprs) => {
                // TODO: Value doesn't have a Tuple variant yet
                for expr in exprs {
                    self.eval_expr(stack_frame, expr)?;
                }
                Ok(self.alloc(ValueData::Uninitialized))
            }

            crate::grammar::Expr::New(class_name, params, field_exprs) => {
                let field_values: Vec<Value> = field_exprs
                    .iter()
                    .map(|e| self.eval_expr(stack_frame, e))
                    .collect::<Result<_, _>>()?;
                self.instantiate_class(class_name, params, &field_values)
            }

            crate::grammar::Expr::Place(crate::grammar::PlaceExpr { place, access }) => {
                let slot = self.resolve_place(stack_frame, place)?;
                match access {
                    crate::grammar::Access::Gv => {
                        // Give: copy the value out. If the value is move
                        // (not copy), uninitialize the source.
                        let copied = self.copy(slot);
                        if !self.is_copy_value(slot) {
                            self.write(slot, ValueData::Uninitialized);
                        }
                        Ok(copied)
                    }
                    crate::grammar::Access::Rf => {
                        // Ref: copy with flag changed to Ref
                        Ok(self.copy_with_flag(slot, ObjectFlag::Ref))
                    }
                    crate::grammar::Access::Mt => {
                        // Mut: create a pointer to the source slot
                        Ok(self.alloc(ValueData::Pointer(slot)))
                    }
                    crate::grammar::Access::Sh => {
                        // Share: copy with flag changed to Shared
                        Ok(self.copy_with_flag(slot, ObjectFlag::Shared))
                    }
                    crate::grammar::Access::Drop => {
                        // Drop: uninitialize the source, unless it's copy.
                        if !self.is_copy_value(slot) {
                            self.write(slot, ValueData::Uninitialized);
                        }
                        Ok(self.alloc(ValueData::Uninitialized))
                    }
                }
            }

            crate::grammar::Expr::Share(expr) => {
                let value = self.eval_expr(stack_frame, expr)?;
                // Change top-level flag to Shared
                match &mut self.values[value.0] {
                    ValueData::Object(obj) => obj.flag = ObjectFlag::Shared,
                    _ => {} // non-objects: sharing is a no-op
                }
                Ok(value)
            }

            crate::grammar::Expr::Call(receiver, method_name, method_params, args) => {
                let receiver_val = self.eval_expr(stack_frame, receiver)?;
                let receiver_data = self.read(self.deref(receiver_val));
                let (class_name, class_parameters) = match receiver_data {
                    ValueData::Object(obj) => match &obj.class {
                        TypeName::Id(id) => (id.clone(), obj.parameters.clone()),
                        _ => anyhow::bail!("cannot call method on non-class type"),
                    },
                    _ => anyhow::bail!("cannot call method on non-object"),
                };
                let arg_vals: Vec<Value> = args
                    .iter()
                    .map(|a| self.eval_expr(stack_frame, a))
                    .collect::<Result<_, _>>()?;
                self.call_method(
                    &class_name,
                    &class_parameters,
                    method_name,
                    method_params,
                    receiver_val,
                    arg_vals,
                )
            }

            crate::grammar::Expr::If(cond, if_true, if_false) => {
                let cond_val = self.eval_expr(stack_frame, cond)?;
                match self.read(cond_val) {
                    ValueData::Int(0) => self.eval_expr(stack_frame, if_false),
                    ValueData::Int(_) => self.eval_expr(stack_frame, if_true),
                    _ => anyhow::bail!("if condition must be an integer"),
                }
            }

            crate::grammar::Expr::Panic => anyhow::bail!("panic!"),

            crate::grammar::Expr::Clear(var) => {
                if let Some(&slot) = stack_frame.variables.get(&Var::Id(var.clone())) {
                    self.write(slot, ValueData::Uninitialized);
                }
                Ok(self.alloc(ValueData::Uninitialized))
            }
        }
    }
}
