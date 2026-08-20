# Statements

Use this guide when you add or review a formalisation. The main question is whether the Lean
statement says what its cited source says.

## Read the source and definitions

Read the cited source, including relevant remarks and variants. Do not treat the module docstring
as an independent source. It is part of the change under review.

Read every non-standard definition used by the statement. Search Mathlib,
`FormalConjecturesForMathlib/`, and nearby files. Confirm names with `#check` and inspect their
definitions before you decide what they return on empty or smallest inputs.

A formalisation can add new definitions. Put a generic, reusable definition in
`FormalConjecturesForMathlib/`. Keep a definition that is specific to one problem in its problem
file. Never add an `axiom`, `opaque`, or `constant` declaration anywhere in the repository.

## Compare the statements

Check:

- the order and scope of all quantifiers
- strict and non-strict bounds
- all hypotheses and domain restrictions
- equality, asymptotic equivalence, and order relations
- the direction of implications
- every variant and special case
- the category and answer recorded by the source

Be careful with `∃ x, P x → Q`. The intended statement is usually `∃ x, P x ∧ Q`; the first
form can be trivially true.

For a yes-or-no problem, check that `answer(True)` states a positive answer and `answer(False)`
states a negative answer. Also check the scope and expected type of `answer(sorry)`. The rest of
the statement must constrain the unknown answer. It must not make the theorem true for every
possible answer.

## Check boundary cases

Substitute the smallest permitted value of each parameter. Check empty types, empty sets, zero,
and missing witnesses. The following table gives common examples. It is not exhaustive.

| Case | Lean behaviour to check |
| --- | --- |
| Empty indexed type or set | A sum is `0`; a function type can be a subsingleton. |
| `ZMod 0` | It is equivalent to `ℤ`, not a finite modulus. |
| `x / 0` | Division returns `0`. |
| `sInf ∅` | The value can be `0`. |

A default value is not a defect by itself. Report it only when the statement can reach that input
and the value changes the mathematical claim.

For each hypothesis, ask whether any object can satisfy it. An impossible hypothesis makes an
implication vacuously true. Add a domain restriction when the source assumes one.
