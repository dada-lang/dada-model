use std::sync::Arc;

use formality_core::{Map, Upcast};

use crate::grammar::{
    ClassDecl, ClassDeclBoundData, ClassPredicate, FieldId, MethodDecl, MethodDeclBoundData,
    MethodId, Parameter, ParameterPredicate, Program, TypeName, ValueId, Var,
};
use crate::type_system::env::Env;
use crate::type_system::predicates::MeetsPredicate;

/// Index into the `Interpreter::values` array.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Value(usize);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ValueData {
    Int(i64),
    Pointer(Value),
    Object(ObjectData),
    Uninitialized,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ObjectData {
    flag: ObjectFlag,
    class: TypeName,
    fields: Map<FieldId, Value>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ObjectFlag {
    Owned,
    Shared,
    Ref,
}

pub struct StackFrame {
    variables: Map<Var, Value>,
}

pub struct Interpreter<'a> {
    program: &'a Program,
    env: Env,
    values: Vec<ValueData>,
}

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

    /// Deep-copy a value into a new slot, recursively copying object fields.
    fn deep_copy(&mut self, value: Value) -> Value {
        let data = self.read(value).clone();
        match data {
            ValueData::Int(_) | ValueData::Uninitialized => self.alloc(data),
            ValueData::Pointer(target) => self.alloc(ValueData::Pointer(target)),
            ValueData::Object(obj) => {
                let new_fields: Map<FieldId, Value> = obj
                    .fields
                    .iter()
                    .map(|(name, &field_val)| (name.clone(), self.deep_copy(field_val)))
                    .collect();
                self.alloc(ValueData::Object(ObjectData {
                    flag: obj.flag,
                    class: obj.class,
                    fields: new_fields,
                }))
            }
        }
    }

    /// Deep-copy a value, changing the top-level object flag.
    fn deep_copy_with_flag(&mut self, value: Value, flag: ObjectFlag) -> Value {
        let copied = self.deep_copy(value);
        match &mut self.values[copied.0] {
            ValueData::Object(obj) => obj.flag = flag,
            _ => {} // non-objects don't have flags
        }
        copied
    }

    /// Resolve a grammar Place to the Value slot it refers to.
    fn resolve_place(&self, stack_frame: &StackFrame, place: &crate::grammar::Place) -> anyhow::Result<Value> {
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

    pub fn interpret(&mut self, class_name: ValueId) -> anyhow::Result<Value> {
        let object = self.instantiate_class(&class_name, &[], &[])?;
        // TODO: find and call main method
        Ok(object)
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
        } = binder.peek();

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
            fields: field_map,
        })))
    }

    fn find_method<'b>(
        &'b self,
        class_name: &ValueId,
        method_id: &MethodId,
    ) -> anyhow::Result<&'b MethodDecl> {
        let ClassDecl {
            name: _,
            class_predicate: _,
            binder,
        } = self.program.class_named(&class_name)?;

        let ClassDeclBoundData {
            predicates: _,
            fields: _,
            methods,
        } = binder.peek();

        methods
            .iter()
            .find(|m| m.name == *method_id)
            .ok_or_else(|| anyhow::anyhow!("class `{:?}` has no method `{:?}`", class_name, method_id))
    }

    fn call_method(
        &mut self,
        class_name: &ValueId,
        method_id: &MethodId,
        this: Value,
        input_values: Vec<Value>,
    ) -> anyhow::Result<Value> {
        let MethodDecl { name: _, binder } = self.find_method(class_name, method_id)?;

        let MethodDeclBoundData {
            this: _,
            inputs,
            output: _,
            predicates: _,
            body,
        } = binder.peek().clone();

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
                        // Give: deep-copy the value out, mark source as Uninitialized
                        let copied = self.deep_copy(slot);
                        // TODO: only uninitialize if not copy
                        self.write(slot, ValueData::Uninitialized);
                        Ok(copied)
                    }
                    crate::grammar::Access::Rf => {
                        // Ref: deep-copy with flag changed to Ref
                        Ok(self.deep_copy_with_flag(slot, ObjectFlag::Ref))
                    }
                    crate::grammar::Access::Mt => {
                        // Mut: create a pointer to the source slot
                        Ok(self.alloc(ValueData::Pointer(slot)))
                    }
                    crate::grammar::Access::Sh => {
                        // Share: deep-copy with flag changed to Shared
                        Ok(self.deep_copy_with_flag(slot, ObjectFlag::Shared))
                    }
                    crate::grammar::Access::Drop => {
                        // Drop: mark source as Uninitialized
                        // TODO: only uninitialize if not copy
                        self.write(slot, ValueData::Uninitialized);
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

            crate::grammar::Expr::Call(receiver, method_name, _params, args) => {
                let receiver_val = self.eval_expr(stack_frame, receiver)?;
                let receiver_data = self.read(self.deref(receiver_val));
                let class_name = match receiver_data {
                    ValueData::Object(obj) => match &obj.class {
                        TypeName::Id(id) => id.clone(),
                        _ => anyhow::bail!("cannot call method on non-class type"),
                    },
                    _ => anyhow::bail!("cannot call method on non-object"),
                };
                let arg_vals: Vec<Value> = args
                    .iter()
                    .map(|a| self.eval_expr(stack_frame, a))
                    .collect::<Result<_, _>>()?;
                self.call_method(&class_name, method_name, receiver_val, arg_vals)
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
