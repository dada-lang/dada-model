test: test-cargo test-book

test-cargo:
    cargo test --all --all-targets

test-book:
    CARGO_TARGET_DIR=target/book cargo build --lib
    mdbook test -L target/book/debug/deps
