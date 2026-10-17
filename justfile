test: test-cargo test-book test-v2

test-cargo:
    cd v1 && just test-cargo

test-book:
    cd v1 && just test-book

book:
    cd v1 && mdbook build

book-v2:
    cd v2 && mdbook build

test-v2:
    cd v2 && cargo test --workspace
