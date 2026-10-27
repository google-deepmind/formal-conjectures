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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1162

*References:*
- [erdosproblems.com/1162](https://www.erdosproblems.com/1162)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
- [Py93] Pyber, L., *Asymptotic results for permutation groups*. Groups and computation
  (New Brunswick, NJ, 1991), DIMACS Ser. Discrete Math. Theoret. Comput. Sci. 11 (1993),
  197-219.
- [RoTr25] Roney-Dougal, C. M. and Tracey, G., *Subgroups of symmetric groups: enumeration and
  asymptotic properties*. [arXiv:2503.05416](https://arxiv.org/abs/2503.05416) (2025).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1162

/-- `f n` is the number of subgroups of the symmetric group $S_n$, realised as
`Equiv.Perm (Fin n)`. All subgroups are counted, not only conjugacy classes. -/
noncomputable def f (n : ℕ) : ℕ := Nat.card (Subgroup (Equiv.Perm (Fin n)))

/-- `f n` is positive. In particular `Real.log (f n)` is not the junk value `Real.log 0`. -/
@[category API, AMS 5 20]
theorem f_pos (n : ℕ) : 0 < f n := by
  unfold f
  exact Nat.card_pos

def erdos_1162.answer : ℕ → ℝ := sorry

/--
Give an asymptotic formula for the number of subgroups of $S_n$. Is there a statistical theorem
on their order?

A problem of Erdős and Turán [Va99, 5.73]. We state the first question: `erdos_1162.answer` is a
function asymptotically equivalent to the number $f(n)$ of subgroups of $S_n$ (an explicit
formula is intended, not $f$ itself). The second question is too vague to state.
-/
@[category research open, question value, AMS 5 20]
theorem erdos_1162 :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] erdos_1162.answer := by
  sorry

/--
Pyber [Py93] proved that
$$\log f(n)\asymp n^2.$$
-/
@[category research solved, AMS 5 20]
theorem erdos_1162.variants.pyber :
    (fun n : ℕ ↦ Real.log (f n : ℝ)) =Θ[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 := by
  sorry

/--
Roney-Dougal and Tracey [RoTr25] have proved that
$$\log f(n)=\left(\frac{1}{16}+o(1)\right)n^2.$$
Here $\log$ is the logarithm to base $2$, as in [RoTr25].
-/
@[category research solved, AMS 5 20]
theorem erdos_1162.variants.roney_dougal_tracey :
    (fun n : ℕ ↦ Real.logb 2 (f n : ℝ)) ~[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 / 16 := by
  sorry

/--
Roney-Dougal and Tracey [RoTr25, Theorem 1] proved that there are absolute constants
$\alpha>0$ and $\beta$ such that for all integers $n>1$
$$2^{n^2/16+\alpha n\log n}\leq f(n)\leq 2^{n^2/16+\beta n^{3/2}},$$
where $\log$ is the logarithm to base $2$. This implies the previous variant.
-/
@[category research solved, AMS 5 20]
theorem erdos_1162.variants.roney_dougal_tracey_bounds :
    ∃ α > (0 : ℝ), ∃ β : ℝ, ∀ n : ℕ, 1 < n →
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + α * n * Real.logb 2 n) ≤ f n ∧
        (f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + β * (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

end Erdos1162
