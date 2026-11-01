# Shared correspondence review

Reviewer: Codex subagent `/root/unique_formalization`. I authored the Unique
formalization and its evaluation checks, but not the Shared or correspondence
implementation reviewed here.

The fifteen `shared.*.json` files contain the final unit-specific correspondence
reviews. `recorded.json` maps units to their accepted immutable evidence records.
Each review supersedes the earlier active records for its unit and lists the
required snapshots plus additional source context actually consulted. These
reviews concern definitions, example setups/results, and theorem statements;
Lean compilation is a separate check.

The review found a distinction worth preserving: a unique reference in a field
reached through shared access can be copied repeatedly, because its first copy
changes the stored reference to shared. The initial wording “giving the same
unique slot twice fails” therefore did not describe the model. The final text
qualifies the claim by the effective mode of the entire path.

`shared.steps-mismatch.json` retains that initial diagnosis. Its recording was
rejected because the source correction arrived first, making the packet stale;
it is not an accepted evidence record. The corrected packet was then prepared,
reviewed, and recorded normally. Other required snapshots were checked unchanged
between those two packet sets.
