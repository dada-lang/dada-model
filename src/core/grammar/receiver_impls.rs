use super::{MethodDecl, Parameter, Perm, ThisDecl};
use crate::dada_lang::{term, try_term};

#[test]
fn core_receiver_accepts_independent_and_origin_permissions() {
    for permission in [
        "given",
        "given[]",
        "given [ ]",
        "shared",
        "shared[]",
        "shared[x]",
        "![x]",
        "given[x]",
        "given[x] ![y]",
    ] {
        let source = format!("{permission} self");
        assert_eq!(term::<ThisDecl>(&source).perm, term::<Perm>(permission));
    }
    assert_eq!(
        format!("{:?}", term::<ThisDecl>("given[] self")),
        "given self"
    );
    assert_eq!(
        format!("{:?}", term::<ThisDecl>("shared[] self")),
        "shared self"
    );
}

#[test]
fn core_receiver_keeps_comments_and_generic_permissions() {
    for source in [
        "given // permission\n self",
        "given [ // no origins\n ] self",
    ] {
        assert_eq!(term::<ThisDecl>(source), ThisDecl::new(Perm::Given));
    }
    let method = term::<MethodDecl>("fn target[perm P](P self, x: P Data) ...;");
    let instantiated = method
        .instantiate_for_call(&[Parameter::perm(Perm::Shared)])
        .unwrap();
    assert_eq!(instantiated.this.perm, Perm::Shared);
}

#[test]
fn owned_receiver_uses_explicit_permission_in_call_diagnostics() {
    let method = term::<MethodDecl>("fn target[perm P](given self, x: P Data) ...;");
    let error = method.instantiate_for_call(&[]).unwrap_err().to_string();
    assert!(error.contains("(given self, x:"), "{error}");
    assert!(!error.contains("self->"), "{error}");
}

#[test]
fn core_receiver_rejects_surface_receiver_sugar() {
    for source in [
        "self",
        "self!",
        "self->",
        "any self",
        "!self",
        "^self",
        "self^",
        "self->!",
        "self!->",
        "given self->",
        "shared self!",
    ] {
        assert!(try_term::<ThisDecl>(source).is_err(), "accepted {source}");
    }
    for source in [
        "fn self.target() ...;",
        "fn self!target[ty T](x: !T) ...;",
        "fn self->target[ty T](x: given T) ...;",
    ] {
        assert!(try_term::<MethodDecl>(source).is_err(), "accepted {source}");
    }
}
