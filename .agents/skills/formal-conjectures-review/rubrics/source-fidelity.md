# Source fidelity

Your job: the Lean statement against the words of the cited source. Read the source, not
only the docstring — the docstring is also under review. A green build tells you nothing
here; a reversed conclusion reads well in both directions. This angle may block.

Named cases below illustrate historical discrepancies, not the status of the current tree.

## What to hunt for

- Quantifiers, the direction of each inequality, the constants, and the ranges. Compare
  each against the source's own phrasing, not the docstring's paraphrase.
- The file contradicting itself. The docstring records the source, so a statement can
  disagree with its own file without the paper in hand. *Erdős 887* `variants.rosenfeld_4`
  (confirmed): the docstring gives the interval `(n^{1/2}, n^{1/2} + n^{1/4})`, coefficient
  `1`; the Lean writes `∃ C > 0, ... C * n^(1/4)`. The two give different answers for the
  greatest `K`; either way the file disagrees with itself.
- A question turned into an assertion, or the wrong half stated. A file can state an
  extremal value as an equality where the source asks whether that value is eventually
  unattainable — with the pigeonhole half already a theorem in the same file, the open
  content is the other half (confirmed; fixed in #4941).
- The shape of a bound. `∃ c > 0, ∀ n, f n ≤ n ^ (c / log log n)` and
  `f(n) < n^{O(1/log log n)}` differ: the first fixes one exponent constant for all `n`,
  the second allows the implied constant to sit outside. Match the source's quantifier
  order over constants.
- Variants: a variant claims the same problem, so run the same comparison. A shared
  definition can make a variant stronger or weaker than its docstring says, and a defect
  in a shared definition affects every statement in the file.

## The positive control

Apply the [evidence rules](../SKILL.md#investigate-consequential-uncertainty) when a claim relies
on a source construction. Use [Lean checking](../references/checking-in-lean.md) only when that
control is needed. A predicate that rejects the source's own example can expose a mismatch.

## Not yours

Whether the hypotheses are satisfiable, junk values, and boundary behaviour belong to
statement-soundness. Category tags, statuses, and `formal_proof` links belong to
metadata-hygiene.

## Review background

Further discussions: [FABLE_REVIEW.md](https://github.com/ryantuck/erdos-ai/blob/master/FABLE_REVIEW.md),
[ryantuck/formal-conjectures#1](https://github.com/ryantuck/formal-conjectures/pull/1),
and FC #4876 and #4896. These are review background, not sources for the mathematical statements.
