/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Borsuk's conjecture

In 1933 Karol Borsuk [Bo33] asked whether every bounded subset of $\mathbb{R}^n$ can be
partitioned into $n + 1$ sets, each of strictly smaller diameter. The hypothesis that the
answer is positive became known as **Borsuk's conjecture**.

The conjecture is true for $n = 2$ [Bo33] and $n = 3$ [Pe47, Eg55]. It is false in general:
Kahn and Kalai [KK93] disproved it for $n = 1325$ and for all $n > 2014$. Bondarenko [Bo14]
gave a counterexample in dimension $65$, and Jenrich and Brouwer [JB14] one in dimension $64$,
the smallest refereed counterexample. In 2026 Grinsztajn [Gr26] posted a 321-point
counterexample in dimension $63$, obtained with AI assistance and verified by exact
computation; the same configuration was found independently by Konz and by Ji [Ji26]. The
cases $4 \leq n \leq 62$ are open. In dimension $4$, every bounded set can be partitioned into
$9$ parts of smaller diameter [La82], and a 2026 preprint reduces this to $8$ parts [TV26].

Formal proofs of the results below that carry a `formal_proof` attribute are available at the
linked locations. Erdős Problem 505
(`FormalConjectures.ErdosProblems.«505»`) points to this file.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Borsuk%27s_conjecture)
- [Bo33] Borsuk, K. (1933). *Drei Sätze über die n-dimensionale euklidische Sphäre*.
  Fundamenta Mathematicae 20, 177–190. https://doi.org/10.4064/fm-20-1-177-190
- [Pe47] Perkal, J. (1947). *Sur la subdivision des ensembles en parties de diamètre inférieur*.
  Colloquium Mathematicum 2, 45.
- [Eg55] Eggleston, H. G. (1955). *Covering a three-dimensional set with sets of smaller
  diameter*. Journal of the London Mathematical Society 30, 11–24.
  https://doi.org/10.1112/jlms/s1-30.1.11
- [La82] Lassak, M. (1982). *An estimate concerning Borsuk partition problem*.
  Bulletin of the Polish Academy of Sciences, Mathematics 30(9–10), 449–451.
- [KK93] Kahn, J., Kalai, G. (1993). *A counterexample to Borsuk's conjecture*.
  Bulletin of the American Mathematical Society 29(1), 60–62.
  https://arxiv.org/abs/math/9307229
- [Bo14] Bondarenko, A. (2014). *On Borsuk's conjecture for two-distance sets*.
  Discrete & Computational Geometry 51(3), 509–515. https://doi.org/10.1007/s00454-014-9579-4
- [JB14] Jenrich, T., Brouwer, A. E. (2014). *A 64-dimensional counterexample to Borsuk's
  conjecture*. Electronic Journal of Combinatorics 21(4), P4.29. https://doi.org/10.37236/4069
- [Gr26] Grinsztajn, M. (2026). *A 63-dimensional counterexample to Borsuk's conjecture*.
  Proof note and verification script, https://github.com/maaxgrin/borsuk-63-counterexample
- [Ji26] Ji, Y. (2026). *An AI generated counterexample to Borsuk problem in dimension 63*.
  https://arxiv.org/abs/2608.12561 (withdrawn as a duplicate of [Gr26])
- [TV26] Tolmachev, A., Voronov, V. (2026). *Reducing the upper bound for the Borsuk number
  in $\mathbb{R}^4$ to 8*. https://arxiv.org/abs/2605.19068
- [OP28a] Tao, T. et al., *Optimization problems*, constant 28a (smallest Borsuk
  counterexample dimension). https://teorth.github.io/optimizationproblems/constants/28a.html
- [Ka15] Kalai, G. (2015). *Some old and new problems in combinatorial geometry I: Around
  Borsuk's problem*. https://arxiv.org/abs/1505.04952
-/

open Metric Bornology

open scoped EuclideanGeometry

namespace Borsuk

variable {E : Type*} [PseudoEMetricSpace E]

/--
`HasBorsukCover k s` means that the set `s` can be covered by `k` sets, each of strictly
smaller extended diameter than `s`.

We use the extended diameter `Metric.ediam` rather than `Metric.diam`: the latter takes the
junk value `0` on unbounded sets, which would make `Set.univ` a covering set of "small"
diameter. With `Metric.ediam`, a set of diameter `0` has no Borsuk cover, and an unbounded
set has no finite Borsuk cover, matching Borsuk's formulation for bounded sets with at
least two points.
-/
def HasBorsukCover (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

/--
**Borsuk's conjecture** in dimension `n`: every bounded subset of $\mathbb{R}^n$ with at
least two points can be partitioned into $n + 1$ sets of strictly smaller diameter.
-/
def BorsukConjecture (n : ℕ) : Prop :=
  ∀ s : Set (ℝ^n), IsBounded s → s.Nontrivial → HasBorsukCover (n + 1) s

/--
**Borsuk's conjecture**, open range: every bounded subset of $\mathbb{R}^n$ with at least two
points can be partitioned into $n + 1$ sets of strictly smaller diameter, for
$4 \leq n \leq 62$.

The conjecture is known to be true for $n \leq 3$ and false for $n \geq 63$.
-/
@[category research open, AMS 52]
theorem borsuk_conjecture (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 62) : BorsukConjecture n := by
  sorry

/-- **Borsuk's conjecture** in dimension $4$, the smallest open case. -/
@[category research open, AMS 52]
theorem borsuk_conjecture.four : BorsukConjecture 4 := by
  sorry

/--
**Partial result in dimension $4$**: every bounded subset of $\mathbb{R}^4$ with at least two
points can be partitioned into $9$ sets of strictly smaller diameter. Proved by Lassak [La82],
who showed more generally that $2^{n-1} + 1$ parts suffice in $\mathbb{R}^n$.
-/
@[category research solved, AMS 52]
theorem borsuk_conjecture.four.nine_parts (s : Set (ℝ^4)) (hs : IsBounded s)
    (hs' : s.Nontrivial) : HasBorsukCover 9 s := by
  sorry

/--
**Partial result in dimension $4$**: every bounded subset of $\mathbb{R}^4$ with at least two
points can be partitioned into $8$ sets of strictly smaller diameter. Claimed by Tolmachev and
Voronov [TV26] via computer-assisted partitions of a truncated Lassak cover, with floating-point
verification; the preprint is not yet refereed.
-/
@[category research solved, AMS 52]
theorem borsuk_conjecture.four.eight_parts (s : Set (ℝ^4)) (hs : IsBounded s)
    (hs' : s.Nontrivial) : HasBorsukCover 8 s := by
  sorry

/-- **Borsuk's conjecture** holds vacuously in dimension $0$: the space is a single point. -/
@[category test, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L118"]
theorem borsuk_conjecture.zero : BorsukConjecture 0 := by
  sorry

/--
**Borsuk's conjecture** in dimension $1$: a bounded set of reals with at least two points
splits at the midpoint of its smallest enclosing interval into two parts of smaller diameter.
-/
@[category textbook, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L126"]
theorem borsuk_conjecture.one : BorsukConjecture 1 := by
  sorry

/-- **Borsuk's conjecture** in the plane, proved by Borsuk [Bo33]. -/
@[category research solved, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L131"]
theorem borsuk_conjecture.two : BorsukConjecture 2 := by
  sorry

/-- **Borsuk's conjecture** in dimension $3$, proved by Perkal [Pe47] and Eggleston [Eg55]. -/
@[category research solved, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L136"]
theorem borsuk_conjecture.three : BorsukConjecture 3 := by
  sorry

/--
**Borsuk's conjecture** is false in general: Kahn and Kalai [KK93] gave counterexamples in
dimension $1325$ and in every dimension $n > 2014$.
-/
@[category research solved, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L144"]
theorem borsuk_conjecture.not_forall : ¬ ∀ n, BorsukConjecture n := by
  sorry

/-- **Borsuk's conjecture** fails in dimension $65$, by Bondarenko [Bo14]. -/
@[category research solved, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L149"]
theorem borsuk_conjecture.not_sixty_five : ¬ BorsukConjecture 65 := by
  sorry

/--
**Borsuk's conjecture** fails in dimension $64$, by Jenrich and Brouwer [JB14]. This is the
smallest dimension with a refereed counterexample.
-/
@[category research solved, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L157"]
theorem borsuk_conjecture.not_sixty_four : ¬ BorsukConjecture 64 := by
  sorry

/--
**Borsuk's conjecture** fails in dimension $63$, by a 321-point configuration found in 2026
by Grinsztajn [Gr26] and independently by Konz and Ji [Ji26]. This is the smallest dimension
in which the conjecture is currently known to be false.
-/
@[category research solved, AMS 52,
  formal_proof using formal_conjectures at
    "https://github.com/mo271/formal-conjectures/blob/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/BorsukConjecture.lean#L166"]
theorem borsuk_conjecture.not_sixty_three : ¬ BorsukConjecture 63 := by
  sorry

end Borsuk
