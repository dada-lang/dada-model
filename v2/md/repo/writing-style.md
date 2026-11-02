# Writing style tenets

Write for a reader who knows language semantics but is new to Dada. The chapter
should explain the model on its own, without requiring the reader to open Lean
or reconstruct earlier design discussions.

## Start with intent

Say what a concept lets us describe or what an operation accomplishes. Then
introduce its representation and rules. For an operation, explain the result
and the change to the state before detailing how to compute them.

## Give the reader something concrete

Use a small example to motivate an unfamiliar distinction. Show the relevant
declarations, action, and result; reuse them as the definitions become more
precise. A table can make related cases easy to compare. Add another example
when it reveals a boundary, such as the difference between an empty field and
one whose status is unknown.

Examples belong in named units and need corresponding Lean cases when
formalized. During Markdown-first review, keep them marked Draft. An example
should help explain a rule, not force the reader to infer the rule.

## Introduce only what the next step needs

Order concepts by their dependencies. Define the machine before discussing its
execution, and define a judgment before stating results about it. Defer a later
layer's machinery until that layer needs it. A short link can record where an
extension belongs without interrupting the current explanation.

## Give every symbol a home

Introduce the term and its metavariable together: “a *statement* \\(t\\).” Give
each symbol a grammar or domain before using it; spell out map domains and
codomains. Distinguish formal syntax from convenient shorthand. When a rule
needs local names, put their definitions beside the rule in a short “where”
clause.

Give named operations and normalization rules their own definition units, so
links land directly on the defining text or equation.
Link uses of named operations and judgments to those definitions, including
uses inside mathematical rules. Leave the defining occurrence unlinked.

## Let prose and mathematics share the work

Use prose to explain purpose and consequences, and mathematics to state the
precise relationship. Avoid narrating every symbol in an equation. Include the
assumptions that determine behavior, and explain a side condition when its role
is easy to miss. Break a long definition where the reader encounters a new
idea, rather than following the boundaries of implementation modules.

## Keep claims inspectable without interrupting the explanation

Put semantic explanations in named units with explicit source references and
dependencies, as described in [Authoring units](authoring.md). Use definitions
for concepts and judgments, and theorems or lemmas for results. State the
result and its assumptions in the book; leave proof checking to Lean.
[Correspondence review](correspondence-review.md) checks whether the formal
statement captures the intended claim. Evidence belongs with that review, so
the narrative can concentrate on the model.

## Edit for a first reading

Prefer short sentences, concrete verbs, and familiar words. Remove repeated
qualifications, announcements of what the next paragraph will say, and praise
for the design. Read the chapter in order and check that each paragraph answers
a question the reader can already understand. Use these tenets to improve that
flow, not as a template that every unit must repeat.
