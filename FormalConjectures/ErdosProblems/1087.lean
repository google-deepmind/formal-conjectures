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
# Erdős Problem 1087

*References:*
- [erdosproblems.com/1087](https://www.erdosproblems.com/1087)
- [ErPu71] Erdős, P. and Purdy, G., *Some extremal problems in geometry*. J. Combinatorial Theory
  Ser. A 10 (1971), 246-252.
-/

@[expose] public section

open Filter Asymptotics
open scoped EuclideanGeometry

namespace Erdos1087

/-- A finite set of points has a repeated distance if two of its pairs of points are the same
distance apart, that is, if it determines fewer distinct distances than it has pairs. -/
def HasRepeatedDistance (S : Finset ℝ²) : Prop :=
  distinctDistances S < S.card.choose 2

open scoped Classical in
/-- The number of degenerate four-element subsets of `P`, that is, those in which two of the six
pairwise distances are equal. -/
noncomputable def degenerateCount (P : Finset ℝ²) : ℕ :=
  ((P.powersetCard 4).filter HasRepeatedDistance).card

/-- $f(n)$: the maximum, over all sets of $n$ points in the plane, of the number of degenerate
four-element subsets. The set of values is nonempty and bounded by $\binom{n}{4}$, so `sSup` is
a true maximum. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ degenerateCount P = m}

/-- A set of `n` points has at most $\binom{n}{4}$ degenerate four-element subsets. -/
@[category API, AMS 52]
theorem degenerateCount_le (P : Finset ℝ²) : degenerateCount P ≤ P.card.choose 4 := by
  classical
  unfold degenerateCount
  exact (Finset.card_filter_le _ _).trans (Finset.card_powersetCard 4 P).le

/-- A set of points has at most `f n` degenerate four-element subsets. -/
@[category API, AMS 52]
theorem degenerateCount_le_f (P : Finset ℝ²) : degenerateCount P ≤ f P.card := by
  refine le_csSup ⟨P.card.choose 4, ?_⟩ ⟨P, rfl, rfl⟩
  rintro m ⟨Q, hQ, rfl⟩
  exact hQ ▸ degenerateCount_le Q

/--
Let $f(n)$ be minimal such that every set of $n$ points in $\mathbb{R}^2$ contains at most $f(n)$
many sets of four points which are 'degenerate' in the sense that some pair are the same distance
apart. Estimate $f(n)$ - in particular, is it true that $f(n)\leq n^{3+o(1)}$?

Here a set of four points is degenerate if two of its six pairwise distances are equal, and
$f(n)\leq n^{3+o(1)}$ is read as $f(n) \ll n^{3+\varepsilon}$ for every $\varepsilon > 0$.
-/
@[category research open, question, AMS 52]
theorem erdos_1087 :
    ∀ ε > (0 : ℝ), (fun n : ℕ ↦ (f n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (3 + ε) := by
  sorry

/--
Erdős and Purdy [ErPu71] proved
$$n^3\log n \ll f(n) \ll n^{7/2}.$$

This is the lower bound.
-/
@[category research solved, AMS 52]
theorem erdos_1087.variants.lower :
    (fun n : ℕ ↦ (n : ℝ) ^ 3 * Real.log n) =O[atTop] fun n : ℕ ↦ (f n : ℝ) := by
  sorry

/--
Erdős and Purdy [ErPu71] proved
$$n^3\log n \ll f(n) \ll n^{7/2}.$$

This is the upper bound.
-/
@[category research solved, AMS 52]
theorem erdos_1087.variants.upper :
    (fun n : ℕ ↦ (f n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (7 / 2 : ℝ) := by
  sorry

end Erdos1087
