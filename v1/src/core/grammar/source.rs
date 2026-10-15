//! Parsable source for core programs, distinct from diagnostic `Debug` output.
//!
//! Binders receive fresh, collision-free source names. Parameters always print
//! an explicit outer permission so reparsing through surface cannot introduce
//! additional permission parameters. Diagnostic `Debug` formatting is unchanged.
//! This renders surface-lowered programs; compiler-internal drop accesses and
//! free formal variables are rejected rather than disguised as source.

use std::collections::{BTreeMap, BTreeSet};

use formality_core::{bail, Fallible, Upcast};

use super::*;

pub fn program(program: &Program) -> Fallible<String> {
    let mut renderer = Renderer::new(program);
    program
        .decls
        .iter()
        .map(|decl| match decl {
            Decl::ClassDecl(class) => renderer.class(class),
        })
        .collect::<Fallible<Vec<_>>>()
        .map(|classes| classes.join("\n\n"))
}

struct Renderer {
    variables: BTreeMap<Variable, String>,
    reserved: BTreeSet<String>,
    next_name: usize,
}

impl Renderer {
    fn new(program: &Program) -> Self {
        // User identifiers are ASCII identifier tokens. Reserving every token
        // in diagnostic output is conservative; the output itself is never
        // reparsed or used to lower/render program structure.
        let reserved = format!("{program:?}")
            .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
            .filter(|name| !name.is_empty())
            .map(str::to_owned)
            .collect();
        Self {
            variables: BTreeMap::new(),
            reserved,
            next_name: 0,
        }
    }

    fn bind(&mut self, variables: &[BoundVar]) -> String {
        let mut declarations = vec![];
        for variable in variables {
            let prefix = match variable.kind {
                Kind::Ty => "__type",
                Kind::Perm => "__perm",
            };
            let name = loop {
                let name = format!("{prefix}{}", self.next_name);
                self.next_name += 1;
                if self.reserved.insert(name.clone()) {
                    break name;
                }
            };
            declarations.push(format!("{:?} {name}", variable.kind));
            self.variables.insert(variable.upcast(), name);
        }
        if declarations.is_empty() {
            String::new()
        } else {
            format!("[{}]", declarations.join(", "))
        }
    }

    fn unbind(&mut self, variables: &[BoundVar]) {
        for variable in variables {
            self.variables.remove(&variable.upcast());
        }
    }

    fn variable(&self, variable: &Variable) -> Fallible<String> {
        self.variables.get(variable).cloned().ok_or_else(|| {
            anyhow::anyhow!("cannot render free variable {variable:?} as closed program source")
        })
    }

    fn class(&mut self, class: &ClassDecl) -> Fallible<String> {
        let (variables, data) = class.binder.open();
        let generics = self.bind(&variables);
        let keyword = match class.class_predicate {
            ClassPredicate::Class => "class",
            ClassPredicate::Struct => "struct",
            ClassPredicate::Shared => "shared struct",
        };
        let mut source = format!(
            "{keyword} {:?}{generics}{} {{\n",
            class.name,
            self.where_clause(&data.predicates)?
        );
        for field in &data.fields {
            let atomic = match field.atomic {
                Atomic::No => "",
                Atomic::Yes => "atomic ",
            };
            source.push_str(&format!(
                "    {atomic}{:?}: {};\n",
                field.name,
                self.ty(&field.ty)?
            ));
        }
        for method in &data.methods {
            source.push_str(&self.method(method)?);
            source.push('\n');
        }
        if !data.drop_body.block.statements.is_empty() {
            source.push_str(&format!(
                "    drop {}\n",
                self.block(&data.drop_body.block, 1)?
            ));
        }
        source.push('}');
        self.unbind(&variables);
        Ok(source)
    }

    fn method(&mut self, method: &MethodDecl) -> Fallible<String> {
        let (variables, data) = method.binder.open();
        let generics = self.bind(&variables);
        let mut inputs = vec![format!("{} self", self.permission(&data.this.perm)?)];
        for input in &data.inputs {
            inputs.push(format!(
                "{:?}: {}",
                input.name,
                self.parameter_type(&input.ty)?
            ));
        }
        let body = match &data.body {
            MethodBody::Trusted => "...;".to_owned(),
            MethodBody::Block(block) => self.block(block, 1)?,
        };
        let result = format!(
            "    fn {:?}{generics}({}) → {}{} {body}",
            method.name,
            inputs.join(", "),
            self.ty(&data.output)?,
            self.where_clause(&data.predicates)?
        );
        self.unbind(&variables);
        Ok(result)
    }

    fn parameter_type(&self, ty: &Ty) -> Fallible<String> {
        match ty {
            Ty::NamedTy(_) => Ok(format!("given {}", self.ty(ty)?)),
            Ty::Var(_) | Ty::ApplyPerm(_, _) => self.ty(ty),
        }
    }

    fn parameters(&self, parameters: &[Parameter], optional: bool) -> Fallible<String> {
        if optional && parameters.is_empty() {
            return Ok(String::new());
        }
        Ok(format!(
            "[{}]",
            parameters
                .iter()
                .map(|p| self.parameter(p))
                .collect::<Fallible<Vec<_>>>()?
                .join(", ")
        ))
    }

    fn parameter(&self, parameter: &Parameter) -> Fallible<String> {
        match parameter {
            Parameter::Ty(ty) => self.ty(ty),
            Parameter::Perm(permission) => self.permission(permission),
        }
    }

    fn ty(&self, ty: &Ty) -> Fallible<String> {
        match ty {
            Ty::Var(variable) => self.variable(variable),
            Ty::ApplyPerm(permission, ty) => {
                Ok(format!("{} {}", self.permission(permission)?, self.ty(ty)?))
            }
            Ty::NamedTy(ty) => match &ty.name {
                TypeName::Tuple(arity) => {
                    if *arity != ty.parameters.len() {
                        bail!("tuple arity differs from its parameters");
                    }
                    let mut types = vec![];
                    for parameter in &ty.parameters {
                        let Parameter::Ty(ty) = parameter else {
                            bail!("tuple contains a permission parameter");
                        };
                        types.push(self.ty(ty)?);
                    }
                    Ok(format!("({})", types.join(", ")))
                }
                TypeName::Int | TypeName::Bool => {
                    if !ty.parameters.is_empty() {
                        bail!("scalar type contains generic parameters");
                    }
                    Ok(format!("{:?}", ty.name))
                }
                TypeName::Array => Ok(format!("Array{}", self.parameters(&ty.parameters, false)?)),
                name => Ok(format!(
                    "{name:?}{}",
                    self.parameters(&ty.parameters, true)?
                )),
            },
        }
    }

    fn permission(&self, permission: &Perm) -> Fallible<String> {
        match permission {
            Perm::Given => Ok("given".to_owned()),
            Perm::Shared => Ok("shared".to_owned()),
            Perm::Mv(places) => Ok(format!("given[{}]", self.places(places)?)),
            Perm::SharedFrom(places) => Ok(format!("shared[{}]", self.places(places)?)),
            Perm::Mt(places) => {
                if places.is_empty() {
                    bail!("mutable permissions require at least one origin");
                }
                Ok(format!("![{}]", self.places(places)?))
            }
            Perm::Var(variable) => self.variable(variable),
            Perm::Apply(left, right) => Ok(format!(
                "{} {}",
                self.permission(left)?,
                self.permission(right)?
            )),
            Perm::Or(alternatives) => Ok(format!(
                "or({})",
                alternatives
                    .iter()
                    .map(|p| self.permission(p))
                    .collect::<Fallible<Vec<_>>>()?
                    .join(", ")
            )),
        }
    }

    fn places(&self, places: &formality_core::Set<Place>) -> Fallible<String> {
        Ok(places
            .iter()
            .map(|p| self.place(p))
            .collect::<Fallible<Vec<_>>>()?
            .join(", "))
    }

    fn place(&self, place: &Place) -> Fallible<String> {
        let mut result = match &place.var {
            Var::This => "self".to_owned(),
            Var::Return => "return".to_owned(),
            Var::InFlight => "@in_flight".to_owned(),
            Var::Magic => "@magic".to_owned(),
            Var::Fresh(index) => format!("@fresh({index})"),
            Var::Id(id) => format!("{id:?}"),
        };
        for projection in &place.projections {
            match projection {
                Projection::Field(field) => result.push_str(&format!(".{field:?}")),
                Projection::Index(index) => result.push_str(&format!("[{index}]")),
            }
        }
        Ok(result)
    }

    fn where_clause(&self, predicates: &[Predicate]) -> Fallible<String> {
        if predicates.is_empty() {
            return Ok(String::new());
        }
        let predicates = predicates
            .iter()
            .map(|predicate| match predicate {
                Predicate::Parameter(kind, parameter) => {
                    Ok(format!("{} is {kind:?}", self.parameter(parameter)?))
                }
                Predicate::Variance(kind, parameter) => {
                    Ok(format!("{} is {kind:?}", self.parameter(parameter)?))
                }
            })
            .collect::<Fallible<Vec<_>>>()?;
        Ok(format!(" where {}", predicates.join(", ")))
    }

    fn block(&self, block: &Block, depth: usize) -> Fallible<String> {
        let mut source = "{\n".to_owned();
        for statement in &block.statements {
            source.push_str(&"    ".repeat(depth + 1));
            source.push_str(&self.statement(statement, depth + 1)?);
            source.push('\n');
        }
        source.push_str(&"    ".repeat(depth));
        source.push('}');
        Ok(source)
    }

    fn statement(&self, statement: &Statement, depth: usize) -> Fallible<String> {
        Ok(match statement {
            Statement::Expr(expr) => format!("{};", self.expr(expr, depth)?),
            Statement::Let(name, ascription, expr) => {
                let ascription = match ascription {
                    Ascription::NoTy => String::new(),
                    Ascription::Ty(ty) => format!(": {}", self.ty(ty)?),
                };
                format!("let {name:?}{ascription} = {};", self.expr(expr, depth)?)
            }
            Statement::Reassign(place, expr) => {
                format!("{} = {};", self.place(place)?, self.expr(expr, depth)?)
            }
            Statement::Drop(place) => format!("drop {};", self.place(place)?),
            Statement::Loop(block) => format!("loop {}", self.block(block, depth)?),
            Statement::Break => "break;".to_owned(),
            Statement::Return(expr) => format!("return {};", self.expr(expr, depth)?),
            Statement::Print(expr) => format!("print({});", self.expr(expr, depth)?),
        })
    }

    fn arguments(&self, arguments: &[Expr], depth: usize) -> Fallible<String> {
        Ok(arguments
            .iter()
            .map(|expr| self.expr(expr, depth))
            .collect::<Fallible<Vec<_>>>()?
            .join(", "))
    }

    fn builtin(
        &self,
        name: &str,
        parameters: &[Parameter],
        arguments: &[&Expr],
        depth: usize,
    ) -> Fallible<String> {
        let arguments = arguments
            .iter()
            .map(|expr| self.expr(expr, depth))
            .collect::<Fallible<Vec<_>>>()?
            .join(", ");
        Ok(format!(
            "{name}{}({arguments})",
            self.parameters(parameters, false)?
        ))
    }

    fn expr(&self, expr: &Expr, depth: usize) -> Fallible<String> {
        Ok(match expr {
            Expr::Block(block) => self.block(block, depth)?,
            Expr::Integer(value) => value.to_string(),
            Expr::True => "true".to_owned(),
            Expr::False => "false".to_owned(),
            Expr::Panic => "!".to_owned(),
            Expr::BinaryOp(left, op, right) => format!(
                "{} {op:?} {}",
                self.expr(left, depth)?,
                self.expr(right, depth)?
            ),
            Expr::Place(place) => {
                if place.place.var == Var::Return {
                    bail!("the return place has no value-expression source spelling");
                }
                let access = match place.access {
                    Access::SharePlace => ".share",
                    Access::Gv => "→",
                    Access::Mt => "!",
                    Access::Drop => {
                        bail!("internal drop access has no value-expression source spelling")
                    }
                };
                format!("{}{access}", self.place(&place.place)?)
            }
            Expr::ShareValue(expr) => format!("{}.share", self.expr(expr, depth)?),
            Expr::Tuple(elements) => format!(
                "({})",
                elements
                    .iter()
                    .map(|expr| self.expr(expr, depth))
                    .collect::<Fallible<Vec<_>>>()?
                    .join(", ")
            ),
            Expr::Call(receiver, method, parameters, arguments) => format!(
                "{}.{method:?}{}({})",
                self.expr(receiver, depth)?,
                self.parameters(parameters, true)?,
                self.arguments(arguments, depth)?
            ),
            Expr::New(name, parameters, arguments) => format!(
                "new {name:?}{}({})",
                self.parameters(parameters, true)?,
                self.arguments(arguments, depth)?
            ),
            Expr::Clear(name) => format!("$clear({name:?})"),
            Expr::If(cond, yes, no) => format!(
                "if {} {} else {}",
                self.expr(cond, depth)?,
                self.expr(yes, depth)?,
                self.expr(no, depth)?
            ),
            Expr::SizeOf(parameters) => self.builtin("size_of", parameters, &[], depth)?,
            Expr::ArrayNew(parameters, capacity) => {
                self.builtin("array_new", parameters, &[capacity], depth)?
            }
            Expr::ArrayCapacity(parameters, array) => {
                self.builtin("array_capacity", parameters, &[array], depth)?
            }
            Expr::ArrayGive(parameters, array, index) => {
                self.builtin("array_give", parameters, &[array, index], depth)?
            }
            Expr::ArrayDrop(parameters, array, start, end) => {
                self.builtin("array_drop", parameters, &[array, start, end], depth)?
            }
            Expr::ArrayWrite(parameters, array, index, value) => {
                self.builtin("array_write", parameters, &[array, index, value], depth)?
            }
            Expr::IsLastRef(parameters, value) => {
                self.builtin("is_last_ref", parameters, &[value], depth)?
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface;

    #[test]
    fn nested_and_shadowed_binders_round_trip_through_surface() {
        let original = surface::parse_program(
            r#"
            struct __type0[type T, perm P] where T is struct {
                value: P T;
                fn outer[type U, perm Q, perm R, perm S](R self, x: S T, y: Q U) → P T
                    where Q is owned, R is mut { x→; }
                fn shadow[type T, perm P](P self, x: given T) → P T ...;
            }
        "#,
        )
        .unwrap();
        let source = program(&original).unwrap();
        assert!(source.contains("struct __type0[type __type1"), "{source}");
        let reparsed = surface::parse_program(&source).unwrap();
        assert_eq!(*reparsed, *original, "{source}");
        assert_eq!(program(&reparsed).unwrap(), source);
    }

    #[test]
    fn generated_permissions_and_nested_shared_types_round_trip() {
        let original = surface::parse_program(r#"
            struct __perm0[type T, perm P] where T is struct {
                field: shared[self] T;
                fn self!generic[type U, perm Q](input: any T, mutable: !given Array[shared[self] U], explicit: Q U)
                    → shared U where U is struct ...;
            }
        "#).unwrap();
        let source = program(&original).unwrap();
        assert!(!source.contains(": any "), "{source}");
        let reparsed = surface::parse_program(&source).unwrap();
        assert_eq!(*reparsed, *original, "{source}");
        assert_eq!(program(&reparsed).unwrap(), source);
    }

    #[test]
    fn defaulted_receiver_and_inputs_print_explicitly() {
        let original = surface::parse_program(
            r#"
            struct Data[type T] where T is struct {
                value: T;
                fn self.defaults[type U](array: Array[T], element: U, explicit: given T) → T ...;
            }
        "#,
        )
        .unwrap();
        let source = program(&original).unwrap();
        let reparsed = surface::parse_program(&source).unwrap();
        assert_eq!(*reparsed, *original, "{source}");
        assert_eq!(program(&reparsed).unwrap(), source);
    }

    #[test]
    fn renderer_preserves_execution_and_explicit_call_arguments() {
        let input = r#"
            struct Data { value: Int; }
            struct Main {
                fn read[perm P, perm Q](P self, x: Q Int) → Int { x→; }
                fn edit[perm P, perm Q](P self, x: Q Data) where P is mut, Q is mut { x.value = 44; }
                fn main(given self) {
                    let actor = new Main();
                    print(actor.share.read[shared[actor], given](22));
                    let data = new Data(0);
                    actor!.edit[![actor], ![data]](data!);
                    print(data.value→);
                    drop data;
                }
            }
        "#;
        let original = surface::parse_program(input).unwrap();
        let source = program(&original).unwrap();
        assert_eq!(
            *surface::parse_program(&source).unwrap(),
            *original,
            "{source}"
        );
        assert_eq!(
            crate::test_util::test_interpret(input)
                .unwrap()
                .to_snapshot(),
            crate::test_util::test_interpret(&source)
                .unwrap()
                .to_snapshot()
        );
    }

    #[test]
    fn expressions_permissions_and_statements_round_trip() {
        // Parser/renderer coverage intentionally includes programs whose bodies
        // are not type-correct; semantic equivalence is tested separately above.
        let original = surface::parse_program(
            r#"
            class Resource {
                value: Int;
                drop { print(self.value→); }
            }
            shared struct Data { value: Int; }
            struct Operations[type T, perm P] where T is struct, T is relative, P is owned {
                atomic value: P T;
                pair: (Int, shared Data);
                flag: Bool;
                empty_array: Array[];
                borrowed: shared[x.field, y[2]] T;
                moved: given[x] T;
                mutable: ![x] T;
                owner: given[] T;
                independent: shared[] T;
                alternatives: or(P, shared) T;
                composed: P shared T;
                fn returning(given self, flag: given Bool) → Bool { return flag→; }
                fn returning_panic(given self) → Bool { return !; }
                fn operations(given self, x: given Array[Int], pair: given(Int, shared Int)) {
                    let array: Array[Int] = array_new[Int](4);
                    array_capacity[Int](array.share);
                    array_write[Int](array!, 0, 1);
                    array_give[Int](array!, 0);
                    array_drop[Int](array!, 0, 1);
                    is_last_ref[shared Data](new Data(0).share);
                    size_of[Int]();
                    let tuple = (1, 2);
                    let singleton = (1,);
                    let nested = ((1,), ());
                    let unit = ();
                    let value = if true { 1 + 2; } else { 3 - 4; };
                    if value→ != 0 { print(false); } else { print(true); };
                    x[0] = 1;
                    tuple;
                    tuple→.share;
                    tuple.share.share;
                    array.share.copy[given]().share;
                    loop { break; }
                    $clear(value);
                    drop array;
                    !;
                }
            }
        "#,
        )
        .unwrap();
        let source = program(&original).unwrap();
        assert_eq!(
            *surface::parse_program(&source).unwrap(),
            *original,
            "{source}"
        );
    }

    #[test]
    fn internal_expression_drop_is_not_printed_as_source() {
        let mut original =
            (*surface::parse_program("struct Main { fn main(given self) { } }").unwrap()).clone();
        let Decl::ClassDecl(class) = &mut original.decls[0];
        let (variables, mut data) = class.binder.open();
        let (method_variables, mut method) = data.methods[0].binder.open();
        method.body = MethodBody::Block(Block {
            statements: vec![Statement::Expr(Expr::Place(PlaceExpr {
                place: Var::This.upcast(),
                access: Access::Drop,
            }))],
        });
        data.methods[0].binder = Binder::new(method_variables, method);
        class.binder = Binder::new(variables, data);
        assert!(program(&original)
            .unwrap_err()
            .to_string()
            .contains("internal drop access"));
        let Decl::ClassDecl(class) = &mut original.decls[0];
        class.binder = class.binder.map(|mut data| {
            data.methods[0].binder = data.methods[0].binder.map(|mut method| {
                method.body = MethodBody::Block(Block {
                    statements: vec![Statement::Expr(Expr::Place(PlaceExpr {
                        place: Var::Return.upcast(),
                        access: Access::Gv,
                    }))],
                });
                method
            });
            data
        });
        assert!(program(&original)
            .unwrap_err()
            .to_string()
            .contains("return place has no value-expression"));
        // Also reject unbound formal variables rather than printing internal
        // de Bruijn names as if they were parsable identifiers.
        let Decl::ClassDecl(class) = &mut original.decls[0];
        let (variables, mut data) = class.binder.open();
        data.fields.push(FieldDecl {
            atomic: Atomic::No,
            name: crate::dada_lang::term("field"),
            ty: Ty::var(BoundVar::fresh(Kind::Ty)),
        });
        class.binder = Binder::new(variables, data);
        assert!(program(&original)
            .unwrap_err()
            .to_string()
            .contains("free variable"));
    }
}
