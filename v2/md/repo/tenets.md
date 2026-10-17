# Repository goals and principles

These principles guide how we develop and explain the specification. Dada's
language design goals are described separately in its
[design goals](../dada/tenets.md).

## Describe results before algorithms

For an operation, first explain the resulting value, changed state, and possible
faults. Then show an algorithm computing that result. Diagrams should let a
reader understand the relationship without mentally running the algorithm.

## Explain execution before static checking

Develop the machine's behavior independently of the type checker. Then explain
how static checking predicts execution and rules out particular failures. This
organization makes conservative rejection and dynamic failure distinguishable.

## Develop several views of the design

English, propositions, examples, code, and proofs illuminate different aspects
of intent. None automatically wins when they disagree. A discrepancy may reveal
ambiguous prose, an inadequate proposition, an implementation defect, or a design
that needs revision. Review makes that discussion explicit.

## Keep evidence inspectable

A reader should be able to follow a claim to the definitions, examples, and
reasoning supporting it. State assumptions and coverage gaps explicitly. Preserve
human and agent review reasoning, and distinguish those judgments from mechanical
proof checking and test results.

## Let the narrative organize the material

The book's structure should serve understanding rather than mirror implementation
modules. Include definitions and local documentation from code where they help
the reader; use authored prose to connect concepts across those definitions.

These are working principles, not claims that the current tooling already
implements all of them.
