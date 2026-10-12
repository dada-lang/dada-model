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
        struct Container[type T, perm P] where T is struct {
            value: P T;

            fn map[perm Q, type U](Q self, x: P T, y: given U) → Q Container[T, P]
                where Q is mut, U is owned {
                let z: P T = x→;
                self.share.other[T, Q](z→, y→);
            }

            fn shadow[type T, perm P](P self, x: given T) → P T {
                x→;
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
        struct Data {
            value: Int;
            fn consume(given self, x: given Int) { x→; }
        }
        class Guard {
            drop { print(1); }
        }
        shared struct Empty {
            fn trusted(shared self) → Int ...;
        }
        "#,
    );
    let class = program.decls[0].as_class_decl().unwrap();
    assert_eq!(class.class_predicate, core::ClassPredicate::Struct);
    let (_, data) = class.binder.open();
    let (generics, method) = data.methods[0].binder.open();
    assert!(generics.is_empty());
    assert_eq!(
        method.inputs[0].ty,
        core::Ty::apply_perm(core::Perm::Given, core::Ty::int())
    );
    assert_eq!(method.output, core::Ty::unit());
}

#[test]
fn expression_and_statement_forms_lower_structurally() {
    // These parser/lowering fixtures intentionally need not type-check. In
    // particular, lowering must remain usable by interpreter-only fault tests.
    for source in [
        "{ let a: Array[shared[x] Int] = new Data[shared](1); a.x = 2; drop a; }",
        "{ loop { break; } true; false; }",
        "if 1 != 2 { print(3); 4 + 5; } else { 6 - 7; }",
        "{ 1 >= 2; 2 <= 3; 3 == 4; }",
        "x!.call[Int, given[x], or(given, ![y])](y.share).share",
        "x→.share",
        "size_of[Array[Int]]()",
        "array_new[Int](3)",
        "array_capacity[Int, shared](x.share)",
        "array_give[Int, given, given](x!, 0)",
        "array_drop[Int, given, given](x!, 0, 1)",
        "array_write[Int, given](x!, 0, 1)",
        "is_last_ref[Int](x.share)",
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
    let source: surface::Statement = dada_lang::term("return (true, 3);");
    let expected = core::Statement::Return(core::Expr::Tuple(vec![
        core::Expr::True,
        core::Expr::Integer(3),
    ]));
    let (actual, _) = desugar::lower_statement(source).into_singleton().unwrap();
    assert_eq!(actual, expected);
}

#[test]
fn tuple_elements_are_comma_separated_in_both_grammars() {
    for (source, arity) in [
        ("()", 0),
        ("(1)", 1),
        ("(1,)", 1),
        ("(1, 2)", 2),
        ("(1, 2,)", 2),
        ("((1,), ())", 2),
        ("(vec!, iter, ())", 3),
        ("(vec→, iter, ())", 3),
        ("(vec!, // separator\n iter, ())", 3),
    ] {
        let parsed: surface::Expr = dada_lang::term(source);
        let expected: core::Expr = dada_lang::term(source);
        let (actual, _) = desugar::lower_expr(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected, "{source}");
        let core::Expr::Tuple(elements) = actual else {
            panic!("expected tuple: {source}")
        };
        assert_eq!(elements.len(), arity, "{source}");
    }
    for source in ["(1 2)", "(vec! other)", "(,)", "(1,,)", "(1, ,2)"] {
        assert!(
            dada_lang::try_term::<surface::Expr>(source).is_err(),
            "{source}"
        );
        assert!(
            dada_lang::try_term::<core::Expr>(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn type_parameters_and_composed_permissions_lower_without_normalization() {
    for source in [
        "Int",
        "given Int",
        "shared[x] ![y] Data[Array[given Int], given[x, y]]",
        "(Int, shared Data, Array[![x] Int])",
        "or(given, ![x]) Int",
    ] {
        let parsed: surface::Ty = dada_lang::term(source);
        let expected: core::Ty = dada_lang::term(source);
        let (actual, _) = desugar::lower_type(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected, "source: {source}");
    }
}

#[test]
fn drop_is_a_statement_and_preserves_its_place_when_lowered() {
    for source in ["drop x;", "drop x.field;", "drop x[0].field;"] {
        let parsed: surface::Statement = dada_lang::term(source);
        let expected: core::Statement = dada_lang::term(source);
        let (actual, _) = desugar::lower_statement(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected);
        assert!(matches!(actual, core::Statement::Drop(_)));
    }
    for source in ["x.drop", "drop x", "drop new Data()"] {
        assert!(
            dada_lang::try_term::<surface::Expr>(source).is_err(),
            "{source}"
        );
    }
    for source in [
        "let y = drop x;",
        "drop x→;",
        "drop x.share;",
        "drop new Data();",
    ] {
        assert!(
            dada_lang::try_term::<surface::Statement>(source).is_err(),
            "{source}"
        );
    }
    assert_program_lowering_is_identity("struct Data { drop { drop self.field; } }");
}

#[test]
fn given_origin_shorthand_lowers_in_outer_and_nested_types() {
    for (source, explicit) in [
        ("[x] Data", "given[x] Data"),
        ("[x.field, y] Data", "given[x.field, y] Data"),
        ("[] Data", "given Data"),
        ("[x] given Data", "given[x] given Data"),
        ("[x] shared[y] Data", "given[x] shared[y] Data"),
        ("[x] [y] Data", "given[x] given[y] Data"),
        ("[x] [y] ![z] Data", "given[x] given[y] ![z] Data"),
        ("given [x] [y] Data", "given[x] given[y] Data"),
        ("shared[x] ![z] [y] Data", "shared[x] ![z] given[y] Data"),
        ("Array[[x] Data]", "Array[given[x] Data]"),
        (
            "[x] (Int, [] Array[[y] Data])",
            "given[x] (Int, given Array[given[y] Data])",
        ),
    ] {
        let parsed: surface::Ty = dada_lang::term(source);
        let expected: core::Ty = dada_lang::term(explicit);
        let (actual, _) = desugar::lower_type(parsed).into_singleton().unwrap();
        assert!(
            actual == expected,
            "{source}\nactual={actual:#?}\nexpected={expected:#?}"
        );
        assert!(
            dada_lang::try_term::<core::Ty>(source).is_err(),
            "core accepted {source}"
        );
    }
}

#[test]
fn given_origin_shorthand_preserves_bound_type_variables() {
    let source = r#"
        class Wrapper[type T] {
            value: [self] T;
            fn method[type U](given self, x: [self] U) → [] Array[U] {
                ();
            }
        }
    "#;
    let explicit = source
        .replace("[self] T", "given[self] T")
        .replace("[self] U", "given[self] U")
        .replace("[] Array", "given Array");
    let parsed: surface::Program = dada_lang::term(source);
    let expected: core::Program = dada_lang::term(&explicit);
    let actual = desugar::program(&parsed).unwrap();
    assert_eq!(actual, expected);
}

#[test]
fn given_origin_shorthand_works_in_call_type_arguments() {
    let parsed: surface::Expr = dada_lang::term("x.method[Array[[x] Data], [] Data]()");
    let expected: core::Expr = dada_lang::term("x.method[Array[given[x] Data], given Data]()");
    let (actual, _) = desugar::lower_expr(parsed).into_singleton().unwrap();
    assert_eq!(actual, expected);
}

#[test]
fn given_origin_shorthand_requires_a_type_and_valid_origins() {
    for source in [
        "[]",
        "[x]",
        "[x, , y] Data",
        "[x→] Data",
        "[new Data()] Data",
    ] {
        assert!(
            dada_lang::try_term::<surface::Ty>(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn retired_permission_spellings_are_not_permission_prefixes() {
    for source in ["ref[x] Data", "mut[x] Data", "^ Data", "given_from[x] Data"] {
        assert!(
            dada_lang::try_term::<surface::Ty>(source).is_err(),
            "{source}"
        );
    }
    for source in ["ref[x]", "mut[x]", "^", "given_from[x]"] {
        assert!(
            dada_lang::try_term::<core::Perm>(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn bool_types_parse_and_lower_like_other_builtins() {
    for source in ["Bool", "given Bool", "Array[Bool]", "shared[self] Bool"] {
        let parsed: surface::Ty = dada_lang::term(source);
        let expected: core::Ty = dada_lang::term(source);
        let (actual, _) = desugar::lower_type(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected);
    }
    assert_program_lowering_is_identity(
        "class Main { fn test(given self, flag: given Bool) → Bool { true; } }",
    );
}

#[test]
fn return_statements_are_unambiguous_with_bare_places() {
    for source in ["return x→;", "return x;", "return true;", "return !;"] {
        let parsed: surface::Statement = dada_lang::term(source);
        let expected: core::Statement = dada_lang::term(source);
        let (actual, _) = desugar::lower_statement(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected);
        assert!(matches!(actual, core::Statement::Return(_)));
    }
    assert_eq!(
        dada_lang::term::<core::Place>("return").var,
        core::Var::Return
    );
    assert!(dada_lang::try_term::<core::ValueId>("return").is_err());
    assert_eq!(
        dada_lang::term::<surface::Statement>("return !;"),
        surface::Statement::Return(surface::Expr::Panic)
    );
    for source in ["return→;", "return.share;", "return.field→;"] {
        assert!(
            dada_lang::try_term::<surface::Statement>(source).is_err(),
            "{source}"
        );
    }
    for source in [
        "given[return] Data",
        "shared[return.field] Data",
        "![return] Data",
    ] {
        let parsed: surface::Ty = dada_lang::term(source);
        let expected: core::Ty = dada_lang::term(source);
        let (actual, _) = desugar::lower_type(parsed).into_singleton().unwrap();
        assert_eq!(actual, expected, "{source}");
    }
}

#[test]
fn applying_permissions_preserves_core_composition_shape() {
    let inner = dada_lang::term::<core::Ty>("shared[x] Data");
    let outer = dada_lang::term::<core::Perm>("given ![y]");
    let expected = dada_lang::term::<core::Ty>("given ![y] shared[x] Data");
    assert_eq!(desugar::apply_permission(outer, inner), expected);
}
