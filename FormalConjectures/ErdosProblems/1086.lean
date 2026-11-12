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
# Erdős Problem 1086

*References:*
- [erdosproblems.com/1086](https://www.erdosproblems.com/1086)
- [ErPu71] Erdős, P. and Purdy, G., *Some extremal problems in geometry*. J. Combinatorial Theory
  Ser. A 10 (1971), 246-252.
- [RaSh17] Raz, O. E. and Sharir, M., *The number of unit-area triangles in the plane: theme and
  variations*. Combinatorica 37 (2017), 1221-1240.
  [arXiv:1501.00379](https://arxiv.org/abs/1501.00379)
-/

@[expose] public section

open Filter Asymptotics
open scoped EuclideanGeometry

namespace Erdos1086

open scoped Classical in
/-- The number of triangles with vertices in `P` and area `a`: the `3`-element subsets of `P`
whose vertices `p, q, r` satisfy `|triangle_area p q r| = a`. -/
noncomputable def triangleAreaCount (P : Finset ℝ²) (a : ℝ) : ℕ :=
  ((P.powersetCard 3).filter fun T =>
    ∃ p q r : ℝ², T = {p, q, r} ∧ |EuclideanGeometry.triangle_area p q r| = a).card

/-- $g(n)$: the maximum, over all sets of $n$ points in the plane and all areas $a > 0$, of the
number of triangles of area $a$ with vertices in the set. Only positive areas count, since every
collinear triple has area $0$. The set of values is nonempty and bounded by $\binom{n}{3}$, so
`sSup` is a true maximum. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (P : Finset ℝ²) (a : ℝ), P.card = n ∧ 0 < a ∧ triangleAreaCount P a = m}

/-- A set of `n` points has at most $\binom{n}{3}$ triangles of any given area. -/
@[category API, AMS 52]
theorem triangleAreaCount_le (P : Finset ℝ²) (a : ℝ) :
    triangleAreaCount P a ≤ P.card.choose 3 := by
  classical
  unfold triangleAreaCount
  exact (Finset.card_filter_le _ _).trans (Finset.card_powersetCard 3 P).le

/-- A set of points has at most `g n` triangles of any given positive area. -/
@[category API, AMS 52]
theorem triangleAreaCount_le_g (P : Finset ℝ²) {a : ℝ} (ha : 0 < a) :
    triangleAreaCount P a ≤ g P.card := by
  refine le_csSup ⟨P.card.choose 3, ?_⟩ ⟨P, a, rfl, ha, rfl⟩
  rintro m ⟨Q, b, hQ, -, rfl⟩
  exact hQ ▸ triangleAreaCount_le Q b

def erdos_1086.answer : ℕ → ℝ := sorry

/--
Let $g(n)$ be minimal such that any set of $n$ points in $\mathbb{R}^2$ contains the vertices of
at most $g(n)$ many triangles with the same area. Estimate $g(n)$.

Only triangles of positive area are counted.
-/
@[category research open, question value, AMS 52]
theorem erdos_1086 : (fun n : ℕ ↦ (g n : ℝ)) =Θ[atTop] erdos_1086.answer := by
  sorry

/--
Erdős and Purdy [ErPu71] proved
$$n^2\log\log n \ll g(n) \ll n^{5/2}.$$

This is the lower bound.
-/
@[category research solved, AMS 52]
theorem erdos_1086.variants.erdos_purdy_lower :
    (fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.log (Real.log n)) =O[atTop] fun n : ℕ ↦ (g n : ℝ) := by
  sorry

/--
The upper bound of Erdős and Purdy [ErPu71] has been improved a number of times. The best known
bound is $g(n) \ll n^{20/9}$ by Raz and Sharir [RaSh17].
-/
@[category research solved, AMS 52]
theorem erdos_1086.variants.raz_sharir :
    (fun n : ℕ ↦ (g n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (20 / 9 : ℝ) := by
  sorry

end Erdos1086
