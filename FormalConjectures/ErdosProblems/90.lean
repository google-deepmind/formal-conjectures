/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 90: The unit distance problem

*Reference:* [erdosproblems.com/90](https://www.erdosproblems.com/90)
-/

open Filter
open EuclideanGeometry
open scoped EuclideanGeometry

namespace Erdos90
open Finset

/--
The set of all possible numbers of unit distances for a configuration of $n$ points.
-/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistancePairsCount points | (points : Finset ℝ²) (_ : points.card = n)}

/--
This lemma confirms that the set of possible unit distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation. The trivial upper bound is
the total number of pairs of points, $\binom{n}{2}$.
-/
@[category test, AMS 52]
theorem unitDistanceCounts_BddAbove (n : ℕ) : BddAbove <| unitDistanceCounts n := by
  unfold Erdos90.unitDistanceCounts
  unfold unitDistancePairsCount
  use n.choose 2
  rintro _ ⟨points, rfl, rfl⟩
  rw [points.card.choose_two_right]
  gcongr
  refine (card_filter_le _ _).trans_eq ?_
  rw [offDiag_card, Nat.mul_sub_left_distrib, mul_one]


/--
The **maximum number of unit distances** determined by any set of $n$ points in the plane.
This function is often denoted as $u(n)$ in combinatorics.
-/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)


/--
Does every set of $n$ distinct points in $\mathbb{R}^2$ contain at most
$n^{1+O(\frac{1}{\log\log n})}$ many pairs which are distance $1$ apart?

This was
[disproved](https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf)
by an internal model at OpenAI, which constructed (for infinitely many $n$) a set $P$ of $n$ points
in $\mathbb{R}^2$ such that the number of unit distance pairs in $P$ is at least $n^{1+c}$, where
$c > 0$ is an absolute constant.
-/
@[category research solved, AMS 52]
theorem erdos_90 : answer(False) ↔ ∃ (O : ℕ → ℝ) (hO : O =O[atTop] (fun n => 1 / (n : ℝ).log.log)),
    (fun n => (maxUnitDistances n : ℝ)) =ᶠ[atTop] fun (n : ℕ) => (n : ℝ) ^ (1 + O n) := by
  sorry

/--
**Constructive form of the disproof.** There is an absolute constant `c > 0` such that
infinitely many `n` admit a configuration realising at least `n^(1+c)` unit distances.

This is the qualitative content of Theorem 1.1 of Alon–Bloom–Gowers–Litt–Sawin–Shankar–
Tsimerman–Wang–Matchett Wood, [*Remarks on the disproof of the unit distance conjecture*](https://arxiv.org/abs/2605.20695)
(2026). An explicit bound `c ≥ 0.014114…` is given by Sawin, [*An explicit lower bound for the unit
distance problem*](https://arxiv.org/abs/2605.20579) (2026); see
`erdos_90.variants.sawin_explicit` below.
-/
@[category research solved, AMS 52]
theorem erdos_90.variants.polynomial_lower_bound :
    ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ (1 + c) ≤ (maxUnitDistances n : ℝ)}.Infinite := by
  sorry

/--
**Sawin's explicit exponent.** The constructive disproof can be realised with `c ≥ 0.014114`
(absorbing the implicit constant `C` of Sawin's Theorem 1 into a slightly smaller exponent for
all large enough `n`). Reference: Theorem 1 of Sawin, [arXiv:2605.20579](https://arxiv.org/abs/2605.20579)
(2026).
-/
@[category research solved, AMS 52]
theorem erdos_90.variants.sawin_explicit :
    {n : ℕ | (n : ℝ) ^ (1 + (14114 : ℝ) / 1000000) ≤ (maxUnitDistances n : ℝ)}.Infinite := by
  sorry

-- TODO(firsching): add the statements from the rest of the page.

end Erdos90
