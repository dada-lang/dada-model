use super::{Expr, Perm, Place, Program, Ty};
use formality_core::test;

#[test]
fn test_parse_program() {
    let p: Program = crate::dada_lang::term(
        "
        struct Point {
            x: Int;
            y: Int;

            fn identity(given self) -> given Point {
                p->;
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
                        class_predicate: Struct,
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
                                drop_body: DropBody {
                                    block: Block {
                                        statements: [],
                                    },
                                },
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
    let p: Perm = crate::dada_lang::term("shared[a.b.c]");
    expect_test::expect![[r#"
        SharedFrom(
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
    let p: Perm = crate::dada_lang::term("shared");
    expect_test::expect![[r#"
        Shared
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_our_perm_with_parens() {
    let p: Perm = crate::dada_lang::term("shared[]");
    expect_test::expect![[r#"
        Shared
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_shared_perm_2() {
    let p: Perm = crate::dada_lang::term("shared[a,b]");
    expect_test::expect![[r#"
        SharedFrom(
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
    let p: Perm = crate::dada_lang::term("given[x]");
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
    let p: Ty = crate::dada_lang::term("shared String");
    expect_test::expect![[r#"
        ApplyPerm(
            Shared,
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
    let p: Ty = crate::dada_lang::term("shared Vec[given U32]");
    expect_test::expect![[r#"
        ApplyPerm(
            Shared,
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
            let x = y.share.foo(bar.share, baz.share);
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
                                    access: SharePlace,
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
                                        access: SharePlace,
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
                                        access: SharePlace,
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

#[test]
fn test_parse_class_with_drop_body() {
    let p: Program = crate::dada_lang::term(
        "
        struct Foo {
            x: Int;

            drop {
                print(self.x->);
            }
        }
    ",
    );
    let class_decl = p.decls[0].as_class_decl().unwrap();
    let (_, bound_data) = class_decl.binder.open();
    expect_test::expect![[r#"
        DropBody {
            block: Block {
                statements: [
                    Print(
                        Place(
                            PlaceExpr {
                                place: Place {
                                    var: This,
                                    projections: [
                                        Field(
                                            x,
                                        ),
                                    ],
                                },
                                access: Gv,
                            },
                        ),
                    ),
                ],
            },
        }
    "#]]
    .assert_debug_eq(&bound_data.drop_body);
}

#[test]
fn test_parse_class_without_drop_body() {
    let p: Program = crate::dada_lang::term(
        "
        struct Foo {
            x: Int;
        }
    ",
    );
    let class_decl = p.decls[0].as_class_decl().unwrap();
    let (_, bound_data) = class_decl.binder.open();
    assert!(bound_data.drop_body.block.statements.is_empty());
}

#[test]
fn test_parse_class_with_methods_and_drop() {
    let p: Program = crate::dada_lang::term(
        "
        struct Foo {
            x: Int;

            fn get(shared self) -> Int {
                self.x->;
            }

            drop {
                print(self.x->);
            }
        }
    ",
    );
    let class_decl = p.decls[0].as_class_decl().unwrap();
    let (_, bound_data) = class_decl.binder.open();
    assert_eq!(bound_data.methods.len(), 1);
    assert!(!bound_data.drop_body.block.statements.is_empty());
}

/// Predicate syntax uses shared for duplicability, while struct remains distinct.
#[test]
fn shared_predicate_vocabulary() {
    use super::ParameterPredicate;
    assert_eq!(
        crate::dada_lang::term::<ParameterPredicate>("shared"),
        ParameterPredicate::Shared
    );
    assert_eq!(
        crate::dada_lang::term::<ParameterPredicate>("struct"),
        ParameterPredicate::Struct
    );
    assert!(crate::dada_lang::try_term::<ParameterPredicate>("copy").is_err());
}

#[test]
fn given_is_no_longer_a_predicate() {
    assert!(crate::dada_lang::try_term::<super::ParameterPredicate>("given").is_err());
    assert!(crate::surface::parse_program("struct given {}").is_err());
}
