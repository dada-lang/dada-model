test: test-cargo test-book

test-cargo:
    cd v1 && just test-cargo

test-book:
    cd v1 && just test-book

book:
    cd v1 && mdbook build
