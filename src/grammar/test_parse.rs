use super::{Expr, Perm, Place, Program, Ty};
use formality_core::test;

#[test]
fn test_parse_program() {
    let p: Program = crate::dada_lang::term(
        "
        class Point {
            x: Int;
            y: Int;

            fn identity(given self) -> given Point {
                p.give;
            }
        }
    ",
    );
    expect_test::expect![[r#"
        Program {
            decls: [
                ClassDecl(
                    ClassDecl {
                        name: Point,
                        class_predicate: Share,
                        binder: Binder {
                            kinds: [],
                            term: ClassDeclBoundData {
                                predicates: [],
                                fields: [
                                    FieldDecl {
                                        atomic: No,
                                        name: x,
                                        ty: NamedTy(
                                            NamedTy {
                                                name: Int,
                                                parameters: [],
                                            },
                                        ),
                                    },
                                    FieldDecl {
                                        atomic: No,
                                        name: y,
                                        ty: NamedTy(
                                            NamedTy {
                                                name: Int,
                                                parameters: [],
                                            },
                                        ),
                                    },
                                ],
                                methods: [
                                    MethodDecl {
                                        name: identity,
                                        binder: Binder {
                                            kinds: [],
                                            term: MethodDeclBoundData {
                                                this: ThisDecl {
                                                    perm: Given,
                                                },
                                                inputs: [],
                                                output: ApplyPerm(
                                                    Given,
                                                    NamedTy(
                                                        NamedTy {
                                                            name: Id(
                                                                Point,
                                                            ),
                                                            parameters: [],
                                                        },
                                                    ),
                                                ),
                                                predicates: [],
                                                body: Block(
                                                    Block {
                                                        statements: [
                                                            Expr(
                                                                Place(
                                                                    PlaceExpr {
                                                                        place: Place {
                                                                            var: Id(
                                                                                p,
                                                                            ),
                                                                            projections: [],
                                                                        },
                                                                        access: Gv,
                                                                    },
                                                                ),
                                                            ),
                                                        ],
                                                    },
                                                ),
                                            },
                                        },
                                    },
                                ],
                            },
                        },
                    },
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_place() {
    let p: Place = crate::dada_lang::term("a.b.c");
    expect_test::expect![[r#"
        Place {
            var: Id(
                a,
            ),
            projections: [
                Field(
                    b,
                ),
                Field(
                    c,
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_shared_perm() {
    let p: Perm = crate::dada_lang::term("ref[a.b.c]");
    expect_test::expect![[r#"
        Rf(
            {
                Place {
                    var: Id(
                        a,
                    ),
                    projections: [
                        Field(
                            b,
                        ),
                        Field(
                            c,
                        ),
                    ],
                },
            },
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_our_perm_without_parens() {
    let p: Perm = crate::dada_lang::term("ref");
    expect_test::expect![[r#"
        Rf(
            {},
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_our_perm_with_parens() {
    let p: Perm = crate::dada_lang::term("ref[]");
    expect_test::expect![[r#"
        Rf(
            {},
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_shared_perm_2() {
    let p: Perm = crate::dada_lang::term("ref[a,b]");
    expect_test::expect![[r#"
        Rf(
            {
                Place {
                    var: Id(
                        a,
                    ),
                    projections: [],
                },
                Place {
                    var: Id(
                        b,
                    ),
                    projections: [],
                },
            },
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_given_from_places_perm() {
    let p: Perm = crate::dada_lang::term("given_from[x]");
    expect_test::expect![[r#"
        Mv(
            {
                Place {
                    var: Id(
                        x,
                    ),
                    projections: [],
                },
            },
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
#[allow(non_snake_case)]
fn test_parse_String_ty() {
    let p: Ty = crate::dada_lang::term("ref String");
    expect_test::expect![[r#"
        ApplyPerm(
            Rf(
                {},
            ),
            NamedTy(
                NamedTy {
                    name: Id(
                        String,
                    ),
                    parameters: [],
                },
            ),
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
#[allow(non_snake_case)]
fn test_parse_Vec_ty() {
    let p: Ty = crate::dada_lang::term("ref Vec[given U32]");
    expect_test::expect![[r#"
        ApplyPerm(
            Rf(
                {},
            ),
            NamedTy(
                NamedTy {
                    name: Id(
                        Vec,
                    ),
                    parameters: [
                        Ty(
                            ApplyPerm(
                                Given,
                                NamedTy(
                                    NamedTy {
                                        name: Id(
                                            U32,
                                        ),
                                        parameters: [],
                                    },
                                ),
                            ),
                        ),
                    ],
                },
            ),
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_expr() {
    let p: Expr = crate::dada_lang::term(
        r#"
        {
            let x = y.ref.foo(bar.ref, baz.ref);
            x = 22;
        }
    "#,
    );
    expect_test::expect![[r#"
        Block(
            Block {
                statements: [
                    Let(
                        x,
                        NoTy,
                        Call(
                            Place(
                                PlaceExpr {
                                    place: Place {
                                        var: Id(
                                            y,
                                        ),
                                        projections: [],
                                    },
                                    access: Rf,
                                },
                            ),
                            foo,
                            [],
                            [
                                Place(
                                    PlaceExpr {
                                        place: Place {
                                            var: Id(
                                                bar,
                                            ),
                                            projections: [],
                                        },
                                        access: Rf,
                                    },
                                ),
                                Place(
                                    PlaceExpr {
                                        place: Place {
                                            var: Id(
                                                baz,
                                            ),
                                            projections: [],
                                        },
                                        access: Rf,
                                    },
                                ),
                            ],
                        ),
                    ),
                    Reassign(
                        Place {
                            var: Id(
                                x,
                            ),
                            projections: [],
                        },
                        Integer(
                            22,
                        ),
                    ),
                ],
            },
        )
    "#]]
    .assert_debug_eq(&p);
}
