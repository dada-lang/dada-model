#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
site_dir="$repo_root/_site"

for tool in cargo mdbook mdbook-mermaid; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        echo "Missing $tool. Install Rust, then run: bash pages/install-tools.sh" >&2
        exit 1
    fi
done

# Rebuild the whole published tree so deleted chapters cannot linger in it.
rm -rf -- "$site_dir"
mkdir -p -- "$site_dir"
cp "$repo_root/pages/index.html" "$site_dir/index.html"
touch "$site_dir/.nojekyll"

for version in v1 v2; do
    (
        cd "$repo_root/$version"
        mdbook build --dest-dir "$site_dir/$version"
    )
    test -s "$site_dir/$version/index.html"
done

echo "Built $site_dir (root redirect, v1, v2)"
