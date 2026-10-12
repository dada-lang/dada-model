use super::{Perm, ReceiverPermission, ThisDecl};
use crate::core::grammar as core;
use crate::dada_lang::{term, try_term};

#[test]
fn explicit_receiver_permissions_parse_with_whitespace_and_comments() {
    for source in [
        "given self",
        "given[] self",
        "given [ ] self",
        "given // permission\n self",
    ] {
        assert_eq!(
            term::<ThisDecl>(source).perm,
            ReceiverPermission::explicit(Perm::Given)
        );
    }
    assert_eq!(
        format!("{:?}", term::<ThisDecl>("given self")),
        "given self"
    );
}

#[test]
fn surface_receiver_keeps_explicit_origin_permissions() {
    for permission in [
        "shared",
        "shared[]",
        "shared[x]",
        "![x]",
        "given[x]",
        "given[x] ![y]",
    ] {
        let source = format!("{permission} // prefix\n self");
        assert_eq!(
            term::<ThisDecl>(&source).perm,
            ReceiverPermission::explicit(term::<Perm>(permission))
        );
    }
}

#[test]
fn receiver_list_rejects_implicit_permissions_and_suffixes() {
    for source in [
        "self",
        "any self",
        "self!",
        "self->",
        "!self",
        "! self",
        "^self",
        "self^",
        "self->!",
        "self!->",
        "self!!",
        "any self!",
        "shared self->",
        "given[x] self!",
    ] {
        assert!(try_term::<ThisDecl>(source).is_err(), "accepted {source}");
        let declaration = format!("struct Data {{ fn method({source}) {{}} }}");
        assert!(
            crate::surface::parse_program(&declaration).is_err(),
            "{declaration}"
        );
    }
}

#[test]
fn header_receiver_sugar_preserves_generated_permission_order() {
    crate::assert_desugars!({
        struct Container[ty T] where T is struct {
            fn self!method[perm P](x: any T, y: !T, z: P T)
                where P is owned ...;
            fn generic[perm P](P self, x: P T) ...;
            fn self->consume(x: given T) ...;
            fn self.defaulted(x: T) ...;
            fn self.any_receiver() ...;
        }
    } => {
        struct Container[ty T] where T is struct {
            fn method[perm P, perm Receiver, perm Input, perm Mutable](Receiver self, x: Input T, y: Mutable T, z: P T)
                where P is owned, Receiver is mut, Mutable is mut ...;
            fn generic[perm P](P self, x: P T) ...;
            fn consume(given self, x: given T) ...;
            fn defaulted[perm Receiver](Receiver self, x: T) ...;
            fn any_receiver[perm Receiver](Receiver self) ...;
        }
    });
}

#[test]
fn owned_receiver_renderer_roundtrips_through_surface() {
    let original = crate::surface::parse_program("struct Data { fn self->method() {} }").unwrap();
    let rendered = core::source::program(&original).unwrap();
    assert!(rendered.contains("fn method(given self)"), "{rendered}");
    assert!(!rendered.contains("self->"), "{rendered}");
    assert_eq!(
        *crate::surface::parse_program(&rendered).unwrap(),
        *original
    );
}
