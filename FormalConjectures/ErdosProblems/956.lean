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
# Erdős Problem 956

*References:*
- [erdosproblems.com/956](https://www.erdosproblems.com/956)
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*. Combinatorica
  **10** (1990), 261-269.
- [Va05] Valtr, P., *The unit-distance problem for convex sets*. Oberwolfach Report 17/2005,
  985-986.
- [Ch26] Chojecki, P., *Erdős Problem 956*.
  [ulam.ai/research/erdos956.pdf](https://www.ulam.ai/research/erdos956.pdf) (April 2026).
- [PALOMAR-2026-10-04-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-04-000008&version=1):
  a Lean 4 proof of the affirmative answer (`erdos_956`) and explicit $\Omega(n^{4/3})$ lower
  bounds (`omega_four_thirds`, `eventual_two_fifths`), checked by Comparator and NanoDa against
  the definitions below and registered with the Palomar registry.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos956

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Minimum Euclidean distance between the sets $C+x$ and $C+y$.
The configurations below require `C.Nonempty`, so neither infimum is empty. -/
noncomputable def translateDistance (C : Set Plane) (x y : Plane) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

/-- A family of pairwise disjoint translates of one nonempty compact convex set.
Lower-dimensional convex sets are allowed. -/
def IsConfiguration (C : Set Plane) (X : Finset Plane) : Prop :=
  C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
    ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint ((· + x) '' C) ((· + y) '' C)

open scoped Classical in
/-- The unordered pairs of distinct centers whose translates have set-distance one. -/
noncomputable def unitPairs (C : Set Plane) (X : Finset Plane) : Finset (Finset Plane) :=
  (X.powersetCard 2).filter fun e =>
    ∃ x y : Plane, x ≠ y ∧ e = {x, y} ∧ translateDistance C x y = 1

/-- The maximum number of unordered unit-distance pairs among $n$ disjoint convex translates.
The attainable counts are bounded by $\binom{n}{2}$, so their supremum is a maximum. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
    X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m}

open scoped Classical in
/-- The number of unit-distance pairs in any configuration on $n$ translates is at most
$\binom{n}{2}$, so the set in the definition of `h n` is bounded above and `h n ≤ n.choose 2`. -/
@[category test, AMS 5 52]
theorem h_le_choose_two (n : ℕ) : h n ≤ n.choose 2 := by
  unfold h unitPairs
  refine csSup_le' ?_
  rintro m ⟨C, X, rfl, -, rfl⟩
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_powersetCard])

/-- With at most one translate there are no two-element subsets of centers, so `h n = 0` for
`n ≤ 1`. -/
@[category test, AMS 5 52]
theorem h_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : h n = 0 := by
  have hle := h_le_choose_two n
  have hchoose : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  omega

/--
Let $h(n)$ be the maximal number of unit distances between $n$ pairwise disjoint translates of a
compact convex set $C \subset \mathbb{R}^2$. Does there exist a constant $c > 0$ such that
$h(n) > n^{1+c}$ for all sufficiently large $n$?

The compact convex body $C$ may depend on $n$. Erdős and Pach [ErPa90] proved the upper bound
$h(n) = O(n^{4/3})$ and posed this superlinear lower-bound question. Valtr [Va05] announced the
matching growth exponent $h(n) = \Theta(n^{4/3})$, and Chojecki [Ch26] gave an explicit Euclidean
parabolic-cap construction. The formal proof registered as [PALOMAR-2026-10-04-000008] proves the
affirmative answer with $c = 1/4$ for the exact definitions above.
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at
    "https://github.com/linrock/math-proofs/blob/2afe25fe500b036dfabef8e00c369a434bfff763/erdos-956/Solution.lean#L61"]
theorem erdos_956 : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ) := by
  sorry

/--
Explicit $\Omega(n^{4/3})$ lower bound: for all $n \ge 80$, $\frac{1}{26} n^{4/3} < h(n)$.
Proved in [PALOMAR-2026-10-04-000008] via a centrally symmetric signed parabolic cap and a
four-layer rectangular grid of disjoint translates.
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at
    "https://github.com/linrock/math-proofs/blob/2afe25fe500b036dfabef8e00c369a434bfff763/erdos-956/Solution.lean#L67"]
theorem erdos_956.variants.omega_four_thirds :
    ∀ n : ℕ, 80 ≤ n → (1 / 26 : ℝ) * (n : ℝ) ^ ((4 : ℝ) / 3) < (h n : ℝ) := by
  sorry

/--
Sharper eventual $\Omega(n^{4/3})$ lower bound: for all sufficiently large $n$ (in fact for all
$n \ge 204{,}525{,}328$), $\frac{2}{5} n^{4/3} < h(n)$. Proved in [PALOMAR-2026-10-04-000008] from
the four-layer signed parabolic grid bound
$h(48q^3 + 16q^2 + 12q + 4) \ge 72q^4 + 32q^3 + 24q^2 + 13q + 3$.
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at
    "https://github.com/linrock/math-proofs/blob/2afe25fe500b036dfabef8e00c369a434bfff763/erdos-956/Solution.lean#L91"]
theorem erdos_956.variants.eventual_two_fifths :
    ∀ᶠ n : ℕ in atTop, (2 / 5 : ℝ) * (n : ℝ) ^ ((4 : ℝ) / 3) < (h n : ℝ) := by
  sorry

/--
Erdős and Pach [ErPa90] proved the upper bound $h(n) = O(n^{4/3})$.
-/
@[category research solved, AMS 5 52]
theorem erdos_956.variants.erdos_pach_upper :
    (fun n : ℕ ↦ (h n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((4 : ℝ) / 3) := by
  sorry

/--
Combining the Erdős–Pach upper bound [ErPa90] (`erdos_956.variants.erdos_pach_upper`) with the
$\Omega(n^{4/3})$ lower bound [Va05, Ch26] (`erdos_956.variants.eventual_two_fifths`) gives
$h(n) = \Theta(n^{4/3})$.
-/
@[category research solved, AMS 5 52]
theorem erdos_956.variants.valtr_theta :
    (fun n : ℕ ↦ (h n : ℝ)) =Θ[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((4 : ℝ) / 3) := by
  refine ⟨erdos_956.variants.erdos_pach_upper, isBigO_iff.mpr ⟨5 / 2, ?_⟩⟩
  filter_upwards [erdos_956.variants.eventual_two_fifths] with n hn
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := by positivity
  have hhnonneg : (0 : ℝ) ≤ (h n : ℝ) := by positivity
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hhnonneg]
  linarith

end Erdos956
