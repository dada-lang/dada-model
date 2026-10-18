test: test-cargo test-book test-v2 test-lean

test-cargo:
    cd v1 && just test-cargo

test-book:
    cd v1 && just test-book

book:
    cd v1 && mdbook build

book-v2:
    cd v2 && mdbook build

book-tools:
    bash pages/install-tools.sh

site:
    bash pages/build.sh

test-v2:
    cd v2 && cargo test --workspace

test-lean:
    cd v2/lean && lake build --wfail
