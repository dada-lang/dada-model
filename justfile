test: test-cargo test-book

test-cargo:
    cargo test --all --all-targets

test-book:
    rm -rf target/book-lib
    CARGO_TARGET_DIR=target/book-lib cargo build --lib
    mdbook test -L target/book-lib/debug/deps
