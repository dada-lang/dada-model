//! Rectilinear routing on corridors around node rectangles.
use anyhow::{Context, Result};
use std::{cmp::Reverse, collections::BinaryHeap};

type Point = (i64, i64);
pub type Rect = (i64, i64, i64, i64);

fn clear(a: Point, b: Point, boxes: &[Rect]) -> bool {
    !boxes.iter().any(|&(x, y, w, h)| {
        if a.0 == b.0 {
            a.0 > x && a.0 < x + w && a.1.min(b.1) < y + h && a.1.max(b.1) > y
        } else {
            a.1 > y && a.1 < y + h && a.0.min(b.0) < x + w && a.0.max(b.0) > x
        }
    })
}

pub fn route(start: Point, end: Point, boxes: &[Rect]) -> Result<Vec<Point>> {
    let mut xs = vec![start.0, end.0];
    let mut ys = vec![start.1, end.1];
    for &(x, y, w, h) in boxes {
        xs.extend([x - 20, x + w + 20]);
        ys.extend([y - 20, y + h + 20]);
    }
    xs.sort_unstable();
    xs.dedup();
    ys.sort_unstable();
    ys.dedup();
    let nx = xs.len();
    let index = |p: Point| -> Result<usize> {
        Ok(
            ys.binary_search(&p.1).ok().context("missing routing y")? * nx
                + xs.binary_search(&p.0).ok().context("missing routing x")?,
        )
    };
    let point = |i: usize| (xs[i % nx], ys[i / nx]);
    let initial = index(start)? * 2;
    let goal = index(end)?;
    let mut costs = vec![i64::MAX; nx * ys.len() * 2];
    let mut previous = vec![None; costs.len()];
    costs[initial] = 0;
    let mut queue = BinaryHeap::from([Reverse((0, initial))]);
    while let Some(Reverse((cost, state))) = queue.pop() {
        if cost != costs[state] {
            continue;
        }
        let node = state / 2;
        if node == goal {
            let mut path = vec![point(node)];
            let mut current = state;
            while let Some(parent) = previous[current] {
                path.push(point(parent / 2));
                current = parent;
            }
            path.reverse();
            let mut compact: Vec<Point> = Vec::new();
            for p in path {
                while compact.len() >= 2 {
                    let a = compact[compact.len() - 2];
                    let b = compact[compact.len() - 1];
                    if (a.0 == b.0 && b.0 == p.0) || (a.1 == b.1 && b.1 == p.1) {
                        compact.pop();
                    } else {
                        break;
                    }
                }
                compact.push(p);
            }
            return Ok(compact);
        }
        let x = node % nx;
        let y = node / nx;
        let neighbors = [
            (x.checked_sub(1).map(|x| y * nx + x), 0),
            ((x + 1 < nx).then_some(node + 1), 0),
            (y.checked_sub(1).map(|y| y * nx + x), 1),
            ((y + 1 < ys.len()).then_some(node + nx), 1),
        ];
        for (next, direction) in neighbors {
            let Some(next) = next else {
                continue;
            };
            let a = point(node);
            let b = point(next);
            if !clear(a, b, boxes) {
                continue;
            }
            let step =
                (a.0 - b.0).abs() + (a.1 - b.1).abs() + if state % 2 == direction { 0 } else { 25 };
            let next_state = next * 2 + direction;
            if cost + step < costs[next_state] {
                costs[next_state] = cost + step;
                previous[next_state] = Some(state);
                queue.push(Reverse((cost + step, next_state)));
            }
        }
    }
    anyhow::bail!("no obstacle-free diagram route from {start:?} to {end:?}")
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn routes_around_boxes_and_through_column_gaps() {
        let boxes = [(100, 0, 80, 80), (100, 140, 80, 80)];
        for (start, end) in [
            ((0, 40), (240, 40)),
            ((0, 110), (240, 110)),
            ((240, 40), (0, 40)),
            ((200, 40), (200, 180)),
        ] {
            let path = route(start, end, &boxes).unwrap();
            assert_eq!(path.first(), Some(&start));
            assert_eq!(path.last(), Some(&end));
            for pair in path.windows(2) {
                assert!(pair[0].0 == pair[1].0 || pair[0].1 == pair[1].1);
                assert!(clear(pair[0], pair[1], &boxes));
            }
        }
        assert_eq!(
            route((0, 110), (240, 110), &boxes).unwrap(),
            vec![(0, 110), (240, 110)]
        );
    }
}
