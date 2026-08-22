# Source fidelity

Your job: the Lean statement against the words of the cited source. Read the source, not
only the docstring — the docstring is also under review. A green build tells you nothing
here; a reversed conclusion reads well in both directions. This angle may block.

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
- Leads needing the cited papers (open in #4896): *Erdős 757*, `IsAdmissible` may use
  `(B - B).ncard = 11` where the source has `11 ≤`; *Erdős 1167*, the module docstring
  records `κ α > r` and the theorem may omit it.
- Variants: a variant claims the same problem, so run the same comparison. A shared
  definition can make a variant stronger or weaker than its docstring says, and a defect
  in a shared definition affects every statement in the file.

## The positive control

Declaring the Lean faithful is a claim like any other, and it carries the same witness duty:
when the source provides a construction, instantiate it against the Lean predicate at a
concrete value (`../references/checking-in-lean.md`). A predicate that rejects the source's
own example is unfaithful in a way no amount of side-by-side reading detects.

## Not yours

Whether the hypotheses are satisfiable, junk values, and boundary behaviour belong to
statement-soundness. Category tags, statuses, and `formal_proof` links belong to
metadata-hygiene.
