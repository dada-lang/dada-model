use mdbook_dada::{evidence, inventory::Inventory};
use std::path::Path;

#[test]
fn evidence_is_complete_and_current() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let inventory = Inventory::load(root)
        .unwrap_or_else(|error| panic!("\n{}", evidence::format_error(&error)));
    let report = evidence::check(&inventory)
        .unwrap_or_else(|error| panic!("\n{}", evidence::format_error(&error)));
    assert!(report.is_ok(), "\n{}", report.render(&inventory));
}
