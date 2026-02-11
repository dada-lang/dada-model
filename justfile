test: test-cargo test-book

test-cargo:
    cargo test --all --all-targets

build-book-preprocessor:
    CARGO_TARGET_DIR=target/book cargo build --bin mdbook-judgment

test-book: build-book-preprocessor
    rm -rf target/book-lib
    CARGO_TARGET_DIR=target/book-lib cargo build --lib
    mdbook test -L target/book-lib/debug/deps
