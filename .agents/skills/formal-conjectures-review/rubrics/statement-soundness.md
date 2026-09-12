# Statement soundness

Your job: whether the statement, read on its own terms, can mean anything at all — and
whether its unknowns are really unknown. A statement with unsatisfiable hypotheses is
true and says nothing; the file builds, the type is correct, and no automatic check
notices. This angle may block.

## What to hunt for

**Hypotheses that cannot hold.** For each hypothesis, ask what must exist, then whether
such a thing exists. *Erdős 80* (confirmed): `Admissible c G` required
`c * n ^ 2 ≤ #G.edgeFinset`; a simple graph on `n` vertices has at most `n(n-1)/2` edges,
so at `c = 2`, `n = 100` that is 20000 against 4950 — the set is empty, `sInf ∅ = 0`, and
both `research open` statements were false (#4867, #4877). *Erdős 694* (confirmed): the
hypothesis quantified `IsGreatest (Nat.totient ⁻¹' {n}) (fmax n)` over every `n`, but the
fibre over `3` is empty, so no `fmax` satisfies it (#4896).

**Junk values.** Lean functions are total; `sInf ∅ = 0` is the junk value that occurs
here. A junk value is not a defect by itself — the question is never "does this
definition have a junk value", it is whether anything reads it at the degenerate input
and whether reaching it changes a claim. Enumerate every declaration that uses the
definition and say what the junk does to each; that table is the deliverable even when
the answer is "nothing breaks". Rules of thumb: junk `0` at the bottom of `ℕ` can only
make an *upper* bound easier — dangerous only for a lower bound, an exact value, or a
`≠ 0` claim — **except** where it sits in the admissibility predicate of an
`∃ a, Admissible a ∧ P a`, where it makes the existential easier and can decide a
`research open` answer. A parameter free at finitely many inputs absorbs junk there; an
`=O`/`=o` at `atTop` cannot see finitely many inputs at all.

**Boundary cases.** Examine the smallest value of each bound. A variant that quantifies
from one below its source's bound can already be decided at that value — two statements
in one file contradicting each other is the cheapest boundary defect to find and the
easiest to read past (confirmed; fixed in #4933). *Green 21* (confirmed):
`fox_kleitman_modular` permits `k = 0`; the hypothesis holds vacuously and the conclusion
becomes `(0 : ZMod p) ≠ 0`, so the answer is `False` for a reason unrelated to the
question. Report what the witness shows *and what it does not show*: in *Erdős 939*
(confirmed, #4934) the `{0, 1}` witness settles `r = 4` only, and `0` is not what blocks
`r = 5` — read `Finset.Coprime` before reasoning about it. A finding that claims too much
costs the reviewer more than no finding.

**`answer()` semantics.**
- *Polarity*: `answer(True) ↔ P` and `answer(False) ↔ P` are opposite claims; compare
  with the source first.
- *Self-answer*: a slot that can take the value it must determine settles nothing.
  *Erdős 195* (confirmed): `answer(sorry) = sSup S` accepts `sSup S`; `AGENTS.md` calls a
  tautological answer no solution, and no check enforces it.
- *Scope*: `answer(sorry) ↔ ∀ᵉ ...` with binders inside the iff is the sanctioned shape
  (`AnswerLinter` recommends it) — do not report it. A section `variable` above the
  declaration is the opposite case and is blocking: the elaborated statement becomes
  `∀ {n}, answer(sorry) ↔ P n`, one Prop cannot match `P n` at every `n`, and where the
  source's `P` is vacuous the slot is forced to `True`, so `answer(False)` is unstatable.
  The linter does not see section variables (#1407); read the binders off the elaborated
  statement. *LatinSquare* (confirmed): two declarations picked up `variable {n : ℕ}`
  and `Odd n → …` is vacuous at even `n` (#5009, #5060).

## Known definition traps

- `Nat.Full k n` is `∀ p ∈ n.primeFactors, p ^ k ∣ n`, and `primeFactors 0 = ∅`, so `0` and `1`
  are vacuously Full. `decide` cannot settle it: the `Decidable` instance exists but does not
  reduce, and gets stuck on `List.decidableBAll` over `primeFactorsList`. Use the lemmas in
  `FormalConjecturesForMathlib/Data/Nat/Full.lean`, which ships `Full.zero_right`,
  `Full.one_right` and a `primeFactorsEq` dsimproc, or `norm_num [Nat.Full, Nat.primeFactors,
  Nat.primeFactorsList]`, which needs `set_option maxRecDepth 4000`; the default 512 fails.
- `Finset.Coprime S` is `S.gcd id = 1`, the gcd of the whole set. It is not pairwise, so a set
  containing `1` is coprime whatever else it holds. Before you propose making it pairwise, check
  the source's own example: for Erdős 939 that example is not pairwise coprime, so the change
  would break it.
- `∑' n, f n` is `0` when `f` is not `Summable`, and `0` is rational, an integer, and a limit.
  So `∃ q : ℚ, ∑' n, f n = q` reads as "converges to a rational **or** diverges". `HasSum`
  carries convergence in the statement and does not have this hole. The same applies to
  `Filter.limsup` over `ℝ`, which is `sInf ∅ = 0` on an unbounded sequence. Check which way it
  cuts: inside a bound this weakens the claim, but inside the admissibility predicate of an
  `∃ a, Admissible a ∧ P a` it makes the existential easier to satisfy, and can make a
  `research open` statement provable.

## Not yours

Whether the statement matches the cited source's words is source-fidelity. Whether an
unfilled slot is *allowed* under the declaration's category, and everything about
`formal_proof`, is metadata-hygiene.
