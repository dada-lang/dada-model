# Publishing the books

The GitHub Pages site has three entry points:

- <https://dada-lang.github.io/dada-model/> — redirects to v2 via `pages/index.html`.
- <https://dada-lang.github.io/dada-model/v1/> — the original Rust model's mdBook.
- <https://dada-lang.github.io/dada-model/v2/> — the evolving literate specification.

The v2 [older versions appendix](../v2/md/appendices/older-versions.md) explains
the earlier approach and links back to the v1 book. The root redirect uses a
relative target and includes a plain link for clients that do not follow redirects.

Chapter paths stay beneath their book's prefix, for example
`/dada-model/v2/operations.html`. Each book's `site-url` in `book.toml` also
sets its 404 page's asset base. Ordinary links and assets remain relative, so
the assembled site can be previewed locally.

## Tools and local preview

Install stable Rust, then run from the repository root:

```sh
just book-tools
just site
python3 -m http.server 8000 --directory _site
```

Open <http://localhost:8000/>. Without `just`, run
`bash pages/install-tools.sh` and `bash pages/build.sh` instead.
The build replaces the generated, ignored `_site/` directory; it does not write
to either book's usual `book/` preview directory.

The installer pins **mdBook 0.5.4** and **mdbook-mermaid 0.17.1**, compatible with
the books' `mdbook-preprocessor` 0.5 API. It skips tools already at those versions.
The v1 `mdbook-judgment` and v2 `mdbook-dada` preprocessors are local Cargo
packages, built automatically by the commands in `book.toml`.
No additional preprocessor binary is needed for v2 mathematics: mdBook loads
MathJax from its CDN. The site build reads Lean source but does not compile it;
Lean checks are a separate validation step.

The v1 Mermaid browser assets (`mermaid.min.js` and `mermaid-init.js`) are
checked in. When upgrading the plugin, review those assets too: installing
the CLI does not update existing assets. The current initializer uses
mdBook 0.5's `mdbook-theme-*` menu IDs.

## GitHub Actions

In the repository's **Settings → Pages → Build and deployment**, the source
must be **GitHub Actions**. The workflow in `.github/workflows/mdbook.yml`:

1. Installs the pinned tools, caching the two binaries.
2. Compiles the v1 library and runs the older book's Rust examples.
3. Runs the same `pages/build.sh` used for local previews.
4. Uploads the complete `_site/` tree as one Pages artifact.
5. Deploys that artifact on pushes to `main`, or a manual run on `main`.

Pull requests build and upload an artifact without deploying. Deployments run
in the `github-pages` environment with Pages and OIDC permissions; build jobs
only need repository read access. The Rust workflow separately tests both
versions' Rust code and lints the v2 preprocessor.

Only committed changes reaching `main` are published. No generated book output
or `gh-pages` branch needs to be committed.
