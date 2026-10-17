#!/usr/bin/env bash
set -euo pipefail

# Keep the CLI versions compatible with the books' mdbook-preprocessor 0.5 API.
# The repository's own preprocessors are built by cargo run from book.toml.
install_tool() {
    local name="$1" version="$2" installed=""
    if command -v "$name" >/dev/null 2>&1; then
        installed="$("$name" --version)"
    fi
    if [[ "$installed" == "$name $version" || "$installed" == "$name v$version" ]]; then
        echo "$name $version is installed"
    else
        cargo install --locked --version "=$version" "$name"
    fi
}

install_tool mdbook 0.5.4
install_tool mdbook-mermaid 0.17.1
