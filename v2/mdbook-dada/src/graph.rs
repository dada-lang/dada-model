//! A small declarative diagram language, not a heap interpreter or invariant checker.
use crate::escape;
use anyhow::{bail, ensure, Context, Result};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
enum Kind {
    Frame,
    Object,
    Primitive,
    Array(usize),
}
#[derive(Debug)]
struct Node {
    id: String,
    label: String,
    kind: Kind,
    slots: Vec<(String, Option<(String, String)>)>,
}

fn identifier(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && chars.all(|c| c.is_alphanumeric() || c == '_')
}

fn args(s: &str) -> Result<Vec<String>> {
    let mut parts = vec![];
    let (mut quoted, mut escaped, mut start) = (false, false, 0);
    for (i, c) in s.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if quoted && c == '\\' {
            escaped = true;
            continue;
        }
        if c == '"' {
            quoted = !quoted;
        }
        if c == ',' && !quoted {
            parts.push(s[start..i].trim().to_owned());
            start = i + 1;
        }
    }
    ensure!(!quoted, "unterminated quoted argument");
    if !s.trim().is_empty() {
        parts.push(s[start..].trim().to_owned());
    }
    Ok(parts)
}
fn label(s: &str) -> Result<String> {
    if s.starts_with('"') {
        Ok(serde_json::from_str::<String>(s)?)
    } else {
        ensure!(
            !s.is_empty() && !s.contains(['(', ')', '"']),
            "invalid argument `{s}`"
        );
        Ok(s.to_owned())
    }
}

fn parse(source: &str) -> Result<Vec<Node>> {
    let mut nodes = Vec::<Node>::new();
    let mut assignments = vec![];
    for (line, text) in source.lines().enumerate() {
        let text = text.trim();
        if text.is_empty() || text.starts_with('#') {
            continue;
        }
        let result = (|| -> Result<()> {
            let (lhs, rhs) = text.split_once('=').context("expected an assignment")?;
            let lhs = lhs.trim();
            let (op, rest) = rhs
                .trim()
                .split_once('(')
                .context("expected constructor(arguments)")?;
            let op = op.trim();
            let arguments = args(
                rest.strip_suffix(')')
                    .context("expected closing parenthesis")?,
            )?;
            if lhs.contains('.') || lhs.contains('[') {
                assignments.push((lhs.to_owned(), op.to_owned(), arguments));
                return Ok(());
            }
            ensure!(identifier(lhs), "invalid node identifier `{lhs}`");
            ensure!(!nodes.iter().any(|n| n.id == lhs), "duplicate node `{lhs}`");
            let (kind, display) = match (op, arguments.as_slice()) {
                ("frame", []) => (Kind::Frame, lhs.to_owned()),
                ("frame", [name]) => (Kind::Frame, label(name)?),
                ("object", [ty]) => (Kind::Object, format!("{} {lhs}", label(ty)?)),
                ("object", [ty, name]) => {
                    (Kind::Object, format!("{} {}", label(ty)?, label(name)?))
                }
                ("primitive", [value]) => (Kind::Primitive, format!("{lhs}: {}", label(value)?)),
                ("primitive", [value, name]) => (
                    Kind::Primitive,
                    format!("{}: {}", label(name)?, label(value)?),
                ),
                ("array", [length]) | ("array", [length, _]) => {
                    let length = length
                        .parse::<usize>()
                        .context("array length must be a nonnegative integer")?;
                    ensure!(length <= 64, "diagram arrays are limited to 64 slots");
                    let name = if arguments.len() == 2 {
                        label(&arguments[1])?
                    } else {
                        lhs.to_owned()
                    };
                    (Kind::Array(length), format!("{name} · length {length}"))
                }
                _ => bail!("unknown constructor or wrong arity: {op}"),
            };
            let slots = if let Kind::Array(n) = kind {
                (0..n).map(|i| (format!("[{i}]"), None)).collect()
            } else {
                vec![]
            };
            nodes.push(Node {
                id: lhs.to_owned(),
                label: display,
                kind,
                slots,
            });
            Ok(())
        })();
        result.with_context(|| format!("heap facts line {}: {text}", line + 1))?;
    }
    ensure!(!nodes.is_empty(), "empty heap diagram");
    let mut seen = BTreeSet::new();
    for (lhs, op, args) in assignments {
        let (owner, slot, indexed) = if let Some((owner, index)) = lhs.split_once('[') {
            let index = index
                .strip_suffix(']')
                .context("expected closing array index")?
                .parse::<usize>()?;
            (owner, format!("[{index}]"), Some(index))
        } else {
            let (owner, slot) = lhs.split_once('.').context("expected node.slot")?;
            ensure!(identifier(slot), "invalid slot name `{slot}`");
            (owner, slot.to_owned(), None)
        };
        ensure!(
            seen.insert((owner.to_owned(), slot.clone())),
            "duplicate slot `{lhs}`"
        );
        let value = match (op.as_str(), args.as_slice()) {
            ("uninitialized", []) => None,
            ("lease" | "leased", [target]) => Some(("leased".to_owned(), target.clone())),
            ("owned" | "showned" | "shlease" | "shared", [target]) => {
                let target_node = nodes
                    .iter()
                    .find(|n| n.id == *target)
                    .with_context(|| format!("unknown target `{target}`"))?;
                ensure!(
                    !matches!(target_node.kind, Kind::Frame),
                    "reference cannot target frame `{target}`"
                );
                // `shared` is a diagram shorthand for a shared lease. Ownership is
                // always spelled `showned`, never inferred from the other edges.
                Some((
                    if op == "shared" {
                        "shlease".to_owned()
                    } else {
                        op
                    },
                    target.clone(),
                ))
            }
            _ => bail!("unknown reference constructor or wrong arity in `{lhs}`"),
        };
        let node = nodes
            .iter_mut()
            .find(|n| n.id == owner)
            .with_context(|| format!("unknown slot owner `{owner}`"))?;
        match (&node.kind, indexed) {
            (Kind::Array(length), Some(index)) => {
                ensure!(index < *length, "array index out of bounds in `{lhs}`");
                node.slots[index].1 = value;
            }
            (Kind::Frame | Kind::Object, None) => node.slots.push((slot, value)),
            _ => bail!("invalid slot projection in `{lhs}`"),
        }
    }
    for node in &nodes {
        for (_, value) in &node.slots {
            if let Some((kind, target)) = value {
                if kind == "leased" {
                    let (n, slot) = edge_target(&nodes, target)?;
                    let edge = nodes[n].slots[slot]
                        .1
                        .as_ref()
                        .context("lease target is uninitialized")?;
                    ensure!(
                        matches!(edge.0.as_str(), "owned" | "leased"),
                        "lease target must be an owned or leased edge: {target}"
                    );
                }
            }
        }
    }
    Ok(nodes)
}

fn edge_target(nodes: &[Node], target: &str) -> Result<(usize, usize)> {
    let (owner, slot) = if let Some((owner, slot)) = target.split_once('.') {
        (owner, slot.to_owned())
    } else if let Some((owner, index)) = target.split_once('[') {
        let index = index
            .strip_suffix(']')
            .context("expected array edge index")?
            .parse::<usize>()?;
        (owner, format!("[{index}]"))
    } else {
        bail!("lease target must name an edge, such as α.f or main.p: {target}");
    };
    let n = nodes
        .iter()
        .position(|n| n.id == owner)
        .with_context(|| format!("unknown edge owner `{owner}`"))?;
    let s = nodes[n]
        .slots
        .iter()
        .position(|(name, _)| *name == slot)
        .with_context(|| format!("unknown edge `{target}`"))?;
    Ok((n, s))
}

pub fn render(source: &str) -> Result<String> {
    let nodes = parse(source)?;
    let lookup: BTreeMap<_, _> = nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.id.as_str(), i))
        .collect();
    // Assign depth by first-discovered owning root path. Cycles and disconnected objects remain
    // renderable; the diagram language does not claim ownership well-formedness.
    let mut depths = vec![None; nodes.len()];
    for (i, n) in nodes.iter().enumerate() {
        if matches!(n.kind, Kind::Frame) {
            depths[i] = Some(0);
        }
    }
    for _ in 0..nodes.len() {
        let mut changed = false;
        for (i, n) in nodes.iter().enumerate() {
            if let Some(depth) = depths[i] {
                for (_, value) in &n.slots {
                    if let Some((kind, target)) = value {
                        if !matches!(kind.as_str(), "owned" | "showned") {
                            continue;
                        }
                        let j = lookup[target.as_str()];
                        if depths[j].is_none() {
                            depths[j] = Some(depth + 1);
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    let width = nodes
        .iter()
        .map(|n| n.label.chars().count())
        .max()
        .unwrap_or(0)
        .max(18) as f64
        * 8.0
        + 32.0;
    let stride = width + 150.0;
    let mut bottoms = BTreeMap::<usize, f64>::new();
    let positions: Vec<_> = nodes
        .iter()
        .enumerate()
        .map(|(i, n)| {
            let depth = depths[i].unwrap_or(1);
            let y = *bottoms.entry(depth).or_insert(30.0);
            let height = 48.0 + 32.0 * n.slots.len() as f64;
            bottoms.insert(depth, y + height + 65.0);
            (30.0 + depth as f64 * stride, y, height)
        })
        .collect();
    let canvas_width = positions
        .iter()
        .map(|(x, _, _)| x + width + 90.0)
        .fold(0.0, f64::max);
    let canvas_height = bottoms.values().copied().fold(0.0, f64::max);
    let mut svg=format!("<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"heap-diagram\" role=\"img\" aria-label=\"Heap objects and references\" viewBox=\"0 0 {canvas_width} {canvas_height}\"><title>Heap objects and references</title><desc>{}</desc>",escape(source));
    for (i, n) in nodes.iter().enumerate() {
        let (x, y, height) = positions[i];
        let class = if matches!(n.kind, Kind::Frame) {
            "heap-frame"
        } else {
            "heap-object"
        };
        svg.push_str(&format!("<g class=\"{class}\"><rect x=\"{x}\" y=\"{y}\" width=\"{width}\" height=\"{height}\" rx=\"6\"/><text x=\"{}\" y=\"{}\" class=\"heap-title\">{}</text>",x+12.0,y+27.0,escape(&n.label)));
        for (s, (slot, value)) in n.slots.iter().enumerate() {
            let sy = y + 62.0 + s as f64 * 32.0;
            let contents = if value.is_none() {
                format!("{slot}: uninitialized")
            } else {
                slot.clone()
            };
            svg.push_str(&format!(
                "<text x=\"{}\" y=\"{sy}\">{}</text>",
                x + 12.0,
                escape(&contents)
            ));
        }
        svg.push_str("</g>");
    }
    for (i, n) in nodes.iter().enumerate() {
        let (x, y, _) = positions[i];
        for (s, (_, value)) in n.slots.iter().enumerate() {
            if let Some((kind, target)) = value {
                let sy = y + 57.0 + s as f64 * 32.0;
                let (tx, ey, edge_targeted) = if kind == "leased" {
                    let (n, slot) = edge_target(&nodes, target)?;
                    let (x, y, _) = positions[n];
                    (x + width + 12.0, y + 57.0 + slot as f64 * 32.0, true)
                } else {
                    let (x, y, height) = positions[lookup[target.as_str()]];
                    (x, sy.clamp(y + 12.0, y + height - 12.0), false)
                };
                let sx = x + width;
                let boxes: Vec<_> = positions
                    .iter()
                    .map(|&(x, y, h)| (x as i64, y as i64, width as i64, h as i64))
                    .collect();
                let route = crate::routing::route(
                    ((sx + 35.0) as i64, sy as i64),
                    (
                        (if edge_targeted { tx } else { tx - 20.0 }) as i64,
                        ey as i64,
                    ),
                    &boxes,
                )?;
                let mut d = format!("M {sx} {sy} H {}", sx + 35.0);
                for &(px, py) in route.iter().skip(1) {
                    d.push_str(&format!(" L {px} {py}"));
                }
                if !edge_targeted {
                    d.push_str(&format!(" L {tx} {ey}"));
                }
                let dot_class = if edge_targeted {
                    "heap-junction"
                } else {
                    "heap-endpoint"
                };
                svg.push_str(&format!("<g class=\"heap-edge {kind}\"><path d=\"{d}\"/><circle class=\"{dot_class}\" cx=\"{tx}\" cy=\"{ey}\" r=\"3\" fill=\"currentColor\"/><text x=\"{}\" y=\"{}\">{kind}</text></g>",sx+5.0,sy-7.0));
            }
        }
    }
    svg.push_str("</svg>");
    Ok(svg)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn facts_render_unicode_fields_and_reference_kinds() {
        let facts="main = frame()\nα = object(Point, \"α\")\nβ = primitive(22)\nmain.p = owned(α)\nmain.q = shared(α)\nα.x = owned(β)";
        let svg = render(facts).unwrap();
        assert!(svg.contains("Point α"));
        assert!(svg.contains("heap-edge shlease"));
        assert_eq!(svg.matches("<g class=\"heap-edge").count(), 3);
        assert_eq!(svg, render(facts).unwrap());
    }
    #[test]
    fn arrays_materialize_uninitialized_slots_and_validate_indices() {
        let nodes = parse("a = array(2)\np = primitive(9)\na[0] = owned(p)").unwrap();
        assert_eq!(nodes[0].slots.len(), 2);
        assert!(nodes[0].slots[1].1.is_none());
        assert!(render("a = array(2)\na[2] = uninitialized()").is_err());
    }
    #[test]
    fn bad_facts_fail_instead_of_silently_changing_the_graph() {
        for facts in [
            "a = frame()\na = frame()",
            "a = frame()\na.p = owned(missing)",
            "a = frame()\na.p = owned(a)",
            "a = primitive(1)\na.x = uninitialized()",
            "a = frame()\na.p = uninitialized()\na.p = uninitialized()",
            "a = unknown()",
        ] {
            assert!(render(facts).is_err(), "{facts}");
        }
    }
    #[test]
    fn labels_are_escaped_and_quoted_commas_are_preserved() {
        let svg = render("a = object(Point, \"<script>, &\\\"\")").unwrap();
        assert!(!svg.contains("<script>"));
        assert!(svg.contains("&lt;script&gt;, &amp;&quot;"));
    }
}

#[cfg(test)]
mod lease_tests {
    use super::*;

    #[test]
    fn leases_join_edges_and_shleases_target_objects() {
        let facts = "main = frame()\nα = object(C)\nβ = primitive(1)\nmain.p = owned(α)\nα.f = owned(β)\nmain.q = lease(α.f)\nmain.r = lease(main.q)\nmain.s = shlease(β)";
        let svg = render(facts).unwrap();
        assert_eq!(svg.matches("class=\"heap-junction\"").count(), 2);
        assert!(svg.contains("heap-edge shlease"));
        for target in ["β", "α.missing", "main.s", "α.empty"] {
            let bad = format!("{facts}\nα.empty = uninitialized()\nmain.bad = lease({target})");
            assert!(render(&bad).is_err(), "{target}");
        }
        assert!(render(
            "main = frame()\na = array(1)\nb = primitive(2)\nmain.q = lease(a[0])\na[0] = owned(b)"
        )
        .is_ok());
        assert!(render(
            "main = frame()\na = primitive(1)\nmain.p = owned(a)\nmain.q = shlease(main.p)"
        )
        .is_err());
    }
}

#[cfg(test)]
mod cycle_tests {
    use super::*;

    #[test]
    fn cycles_self_loops_and_disconnected_cycles_render_deterministically() {
        let rect = regex::Regex::new(
            r#"<rect x="([\d.]+)" y="([\d.]+)" width="([\d.]+)" height="([\d.]+)""#,
        )
        .unwrap();
        let paths = regex::Regex::new(r#"<path d="([^"]+)""#).unwrap();
        for facts in [
            "a = object(Node)\na.next = showned(a)",
            "a = object(Node)\nb = object(Node)\na.next = showned(b)\nb.next = showned(a)",
            "main = frame()\na = object(Node)\nb = object(Node)\nmain.p = showned(a)\na.next = showned(b)\nb.next = showned(a)",
        ] {
            let svg = render(facts).unwrap();
            assert_eq!(svg, render(facts).unwrap());
            assert!(!svg.contains("NaN"));
            assert!(!svg.contains("heap-arrow"));
            let nodes = parse(facts).unwrap();
            let count = nodes.iter().flat_map(|n| &n.slots).filter(|(_, v)| v.is_some()).count();
            assert_eq!(svg.matches("class=\"heap-endpoint\"").count(), count);
            // Check every routed segment against every rendered rectangle, including
            // the source and destination: only boundary contact is permitted.
            let boxes: Vec<Vec<f64>> = rect.captures_iter(&svg).map(|c| (1..=4).map(|i| c[i].parse().unwrap()).collect()).collect();
            for c in paths.captures_iter(&svg) {
                let mut tokens = c[1].split_whitespace();
                let mut last = (0.0_f64, 0.0_f64);
                while let Some(op) = tokens.next() {
                    let x: f64 = tokens.next().unwrap().parse().unwrap();
                    let next = if op == "H" { (x,last.1) } else { (x,tokens.next().unwrap().parse().unwrap()) };
                    if op != "M" {
                        assert!(last.0 == next.0 || last.1 == next.1);
                        for b in &boxes {
                            let crosses = if last.0 == next.0 {
                                last.0 > b[0] && last.0 < b[0]+b[2] && last.1.min(next.1) < b[1]+b[3] && last.1.max(next.1) > b[1]
                            } else {
                                last.1 > b[1] && last.1 < b[1]+b[3] && last.0.min(next.0) < b[0]+b[2] && last.0.max(next.0) > b[0]
                            };
                            assert!(!crosses, "edge crosses box in {facts}");
                        }
                    }
                    last = next;
                }
            }
        }
    }
}
