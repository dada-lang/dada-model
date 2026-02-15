use formality_core::{Map, Upcast};

use crate::grammar::{
    ClassDecl, ClassDeclBoundData, ClassPredicate, FieldId, MethodDecl, MethodDeclBoundData,
    Program, TypeName, ValueId, Var,
};

pub struct Interpreter<'a> {
    program: &'a Program,
}

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program) -> Self {
        Self { program }
    }

    pub fn interpreter(&self, class_name: ValueId) -> anyhow::Result<Value> {
        let object = self.instantiate_class(&class_name, &[])?;
    }

    fn instantiate_class(
        &self,
        class_name: &ValueId,
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

        if fields.len() != fields.len() {
            anyhow::bail!(
                "class `{:?}` has {} fields but {} were provided",
                class_name,
                fields.len(),
                fields.len()
            );
        }

        let field_map = fields
            .iter()
            .zip(field_values)
            .map(|(field_decl, value)| (field_decl.name.clone(), value.clone()))
            .collect();

        let flag = match class_predicate {
            ClassPredicate::Guard => ObjectFlag::Owned,
            ClassPredicate::Share => ObjectFlag::Owned,
            ClassPredicate::Shared => ObjectFlag::Shared,
        };

        Ok(Value::Object(ObjectData {
            flag,
            class: class_name.upcast(),
            fields: field_map,
        }))
    }

    fn find_method(
        &self,
        class_name: &ValueId,
        method_id: &ValueId,
    ) -> anyhow::Result<&MethodDecl> {
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
            .find(|m| &m.name[..] == "main")
            .ok_or_else(|| anyhow::anyhow!("class `{:?}` has no main method", class_name))
    }

    fn call_method(
        &self,
        class_name: &ValueId,
        method_id: &ValueId,
        this: Value,
        input_values: Vec<Value>,
    ) -> anyhow::Result<Value> {
        let MethodDecl { name: _, binder } = self.find_method(class_name, method_id)?;

        let MethodDeclBoundData {
            this: _,
            inputs,
            output,
            predicates: _,
            body,
        } = binder.peek();

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
                .insert(input.name.clone(), input_value);
        }

        match body {
            crate::grammar::MethodBody::Trusted => anyhow::bail!(
                "method `{:?}` of class `{:?}` is trusted and cannot be called by the interpreter",
                method_id,
                class_name
            ),
            crate::grammar::MethodBody::Block(block) => self.eval_block(&mut stack_frame, block),
        }
    }

    fn eval_block(
        &self,
        stack_frame: &mut StackFrame,
        block: &crate::grammar::Block,
    ) -> anyhow::Result<Value> {
        let crate::grammar::Block { statements } = block;

        let mut final_value = Value::Unitialized;
        for statement in statements {
            final_value = self.eval_statement(stack_frame, statement)?;
        }
        Ok(final_value)
    }

    fn eval_statement(
        &self,
        stack_frame: &mut StackFrame,
        statement: &crate::grammar::Statement,
    ) -> anyhow::Result<Value> {
        match statement {
            crate::grammar::Statement::Expr(expr) => self.eval_expr(stack_frame, expr),
            crate::grammar::Statement::Let { name, value } => {
                let value = self.eval_expr(stack_frame, value)?;
                stack_frame.variables.insert(name.clone(), value);
                Ok(Value::Uninitialized)
            }
        }
    }
}

pub struct StackFrame {
    variables: Map<Var, Value>,
}

pub struct Heap {
    objects: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Value {
    Int(i64),
    Pointer(usize),
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
}
