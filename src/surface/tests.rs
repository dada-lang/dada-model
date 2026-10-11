use crate::{core::grammar as core, dada_lang};

use super::{desugar, grammar as surface};

fn assert_program_lowering_is_identity(source: &str) -> core::Program {
    let surface: surface::Program = dada_lang::term(source);
    let expected: core::Program = dada_lang::term(source);
    let actual = desugar::program(&surface).expect("surface program lowers");
    assert_eq!(actual, expected);
    actual
}

#[test]
fn nested_binders_preserve_scopes_and_generic_order() {
    let program = assert_program_lowering_is_identity(
        r#"
        class Container[ty T, perm P] where T is share {
            value: P T;

            fn map[perm Q, ty U](Q self, x: P T, y: U) -> Q Container[T, P]
                where Q is mut, U is owned {
                let z: P T = x.give;
                self.ref.other[T, Q](z.give, y.give);
            }

            fn shadow[ty T, perm P](P self, x: T) -> P T {
                x.give;
            }
        }
        "#,
    );
    let class = program.decls[0].as_class_decl().unwrap();
    assert_eq!(class.binder.kinds(), &[core::Kind::Ty, core::Kind::Perm]);
    let (_, data) = class.binder.open();
    assert_eq!(
        data.methods[0].binder.kinds(),
        &[core::Kind::Perm, core::Kind::Ty]
    );
    assert_eq!(
        data.methods[1].binder.kinds(),
        &[core::Kind::Ty, core::Kind::Perm]
    );
}

#[test]
fn current_defaults_and_declaration_categories_are_unchanged() {
    let program = assert_program_lowering_is_identity(
        r#"
        class Data {
            value: Int;
            fn consume(^ self, x: Int) { x.give; }
        }
        given class Guard {
            drop { print(1); }
        }
        shared class Empty {
            fn trusted(shared self) -> Int ...;
        }
        "#,
    );
    let class = program.decls[0].as_class_decl().unwrap();
    assert_eq!(class.class_predicate, core::ClassPredicate::Share);
    let (_, data) = class.binder.open();
    let (generics, method) = data.methods[0].binder.open();
    assert!(generics.is_empty());
    assert_eq!(method.inputs[0].ty, core::Ty::int());
    assert_eq!(method.output, core::Ty::unit());
}

#[test]
fn expression_and_statement_forms_lower_structurally() {
    // These parser/lowering fixtures intentionally need not type-check. In
    // particular, lowering must remain usable by interpreter-only fault tests.
    for source in [
        "{ let a: Array[shared[x] Int] = new Data[shared](1); a.x = 2; a.drop; }",
        "{ loop { break; } true; false; }",
        "if 1 != 2 { print(3); 4 + 5; } else { 6 - 7; }",
        "{ 1 >= 2; 2 <= 3; 3 == 4; }",
        "x.mut.call[Int, ^[x], or(^, ![y])](y.ref).share",
        "x.give.share",
        "size_of[Array[Int]]()",
        "array_new[Int](3)",
        "array_capacity[Int, shared](x.ref)",
        "array_give[Int, ^, ^](x.mut, 0)",
        "array_drop[Int, ^, ^](x.mut, 0, 1)",
        "array_write[Int, ^](x.mut, 0, 1)",
        "is_last_ref[Int](x.ref)",
        "$clear(x)",
        "!",
    ] {
        let parsed: surface::Expr = dada_lang::term(source);
        let expected: core::Expr = dada_lang::term(source);
        let (actual, _) = desugar::lower_expr(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected, "source: {source}");
    }
}

#[test]
fn return_and_tuple_nodes_lower_structurally() {
    // Construct these nodes directly: the existing parser does not reserve
    // `return`, so its place-variable and identifier productions are ambiguous.
    let source = surface::Statement::Return(surface::Expr::Tuple(vec![
        surface::Expr::True,
        surface::Expr::Integer(3),
    ]));
    let expected = core::Statement::Return(core::Expr::Tuple(vec![
        core::Expr::True,
        core::Expr::Integer(3),
    ]));
    let (actual, _) = desugar::lower_statement(source).into_singleton().unwrap();
    assert_eq!(actual, expected);
}

#[test]
fn type_parameters_and_composed_permissions_lower_without_normalization() {
    for source in [
        "Int",
        "^ Int",
        "shared[x] ![y] Data[Array[^ Int], ^[x, y]]",
        "(Int, shared Data, Array[![x] Int])",
        "or(^, ![x]) Int",
    ] {
        let parsed: surface::Ty = dada_lang::term(source);
        let expected: core::Ty = dada_lang::term(source);
        let (actual, _) = desugar::lower_type(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected, "source: {source}");
    }
}
