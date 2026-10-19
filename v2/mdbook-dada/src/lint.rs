//! Source-level LaTeX conventions, including literal examples in Markdown.

use anyhow::{ensure, Result};
use regex::Regex;

/// Require an opening group immediately before each overbar command and a
/// literal space immediately after it. Longer TeX control words are separate commands.
pub fn check_latex(source: &str, path: &str) -> Result<()> {
    let overline = Regex::new(r"\\overline([^A-Za-z]|$)")?;
    for matched in overline.captures_iter(source) {
        let command = matched.get(0).expect("a regex match has a full capture");
        let line = source[..command.start()]
            .bytes()
            .filter(|&byte| byte == b'\n')
            .count()
            + 1;
        ensure!(
            source[..command.start()].ends_with('{') && &matched[1] == " ",
            "{path}:{line}: LaTeX style: use {{\\overline f}}; the command must be immediately preceded by `{{` and immediately followed by a literal space"
        );
    }
    Ok(())
}
