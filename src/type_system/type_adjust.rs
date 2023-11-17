use contracts::ensures;

use crate::grammar::{Perm, Ty};

impl Ty {
    /// A *simplified* type has at most one level of permission (which is also simple).
    pub fn is_simplified(&self) -> bool {
        let mut p = self;

        if let Ty::ApplyPerm(perm, ty) = p {
            if !perm.is_simplified() {
                return false;
            }
            p = ty;
        }

        matches!(p, Ty::ClassTy(_) | Ty::Var(_))
    }

    /// A *simplified* type meets the grammar `Perm? (base type)`.
    /// To create a simplified type, we accumulate the permissions and simplify.
    // #[ensures(ret.is_simplified())]
    pub fn simplify(&self) -> Ty {
        match self {
            Ty::ClassTy(_) | Ty::Var(_) => self.clone(),
            Ty::ApplyPerm(perm0, ty) => {
                let perm0 = perm0.simplify();
                let ty = ty.simplify();
                if let Ty::ApplyPerm(perm1, ty1) = ty {
                    let perm2 = perm0.rebase(perm1).simplify();
                    Ty::apply_perm(perm2, ty1)
                } else {
                    Ty::apply_perm(perm0, ty)
                }
            }
        }
    }
}

impl Perm {
    pub fn is_simplified(&self) -> bool {
        let mut perm = self;

        // Simplified perms can start with a shared
        if let Self::Shared(_, perm1) = perm {
            perm = perm1;
        }

        // They can then have any number of leases or variables
        while let Self::Leased(_, perm1) | Self::Var(_, perm1) = perm {
            perm = perm1;
        }

        // And finally an owned
        matches!(perm, Perm::Owned)
    }

    /// A *simplified* permission meets the grammar `shared(_)? leased(_)* var(_)* my`.
    /// To create a simplified perm, we apply the rules that sharing or leasing a shared thing
    /// just results in the original shared thing. Otherwise, we preserve what is there.
    #[ensures(ret.is_simplified())]
    pub fn simplify(&self) -> Perm {
        match self {
            Perm::Owned => Perm::Owned,
            Perm::Var(var, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::var(var, perm)
                }
            }
            Perm::Shared(places, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::shared(places, perm)
                }
            }
            Perm::Leased(places, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::leased(places, perm)
                }
            }
        }
    }
}

#[test]
fn shared_leased() {
    use crate::dada_lang::term;
    let p: Perm = term("shared(x) leased(y) owned");
    assert!(p.is_simplified());
    expect_test::expect![[r#"
        Shared(
            [
                Place {
                    var: x,
                    projections: [],
                },
            ],
            Leased(
                [
                    Place {
                        var: y,
                        projections: [],
                    },
                ],
                Owned,
            ),
        )
    "#]]
    .assert_debug_eq(&p.simplify());
}

#[test]
fn leased_shared_leased() {
    use crate::dada_lang::term;

    let p: Perm = term("leased(x) shared(y) leased(z) owned");
    assert!(!p.is_simplified());
    expect_test::expect![[r#"
        Shared(
            [
                Place {
                    var: y,
                    projections: [],
                },
            ],
            Leased(
                [
                    Place {
                        var: z,
                        projections: [],
                    },
                ],
                Owned,
            ),
        )
    "#]]
    .assert_debug_eq(&p.simplify());
}

#[test]
fn leased_shared_leased_ty() {
    use crate::dada_lang::grammar::Binder;
    use crate::dada_lang::term;
    let p: Ty = term("shared(y) leased(z) owned String");
    let t: Binder<Ty> = term("[ty X] leased(x) X");
    let u = t.instantiate_with(&[p]).unwrap();
    assert!(!u.is_simplified());

    // Immediately after substituting, we have `leased(x) (shared(y) leased(z) owned String)`
    expect_test::expect![[r#"
        ApplyPerm(
            Leased(
                [
                    Place {
                        var: x,
                        projections: [],
                    },
                ],
                Owned,
            ),
            ApplyPerm(
                Shared(
                    [
                        Place {
                            var: y,
                            projections: [],
                        },
                    ],
                    Leased(
                        [
                            Place {
                                var: z,
                                projections: [],
                            },
                        ],
                        Owned,
                    ),
                ),
                ClassTy(
                    ClassTy {
                        name: Id(
                            String,
                        ),
                        parameters: [],
                    },
                ),
            ),
        )
    "#]]
    .assert_debug_eq(&u);

    // Simplifying, we get just `shared(y) leased(z) owned String`
    expect_test::expect![[r#"
        ApplyPerm(
            Shared(
                [
                    Place {
                        var: y,
                        projections: [],
                    },
                ],
                Leased(
                    [
                        Place {
                            var: z,
                            projections: [],
                        },
                    ],
                    Owned,
                ),
            ),
            ClassTy(
                ClassTy {
                    name: Id(
                        String,
                    ),
                    parameters: [],
                },
            ),
        )
    "#]]
    .assert_debug_eq(&u.simplify());
}
