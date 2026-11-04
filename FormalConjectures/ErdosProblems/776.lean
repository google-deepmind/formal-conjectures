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
# Erdős Problem 776

*References:*
- [erdosproblems.com/776](https://www.erdosproblems.com/776)
- [HeTa26] He, Y. and Tang, Q., *An Erdős–Trotter problem on antichains with multiplicity
  $r$ on each occurring level*. [arXiv:2602.09803v2](https://arxiv.org/abs/2602.09803v2)
  (2026).
-/

@[expose] public section

open Filter

namespace Erdos776

-- Set of subsets of [n]
abbrev Family (n : ℕ) := Finset (Finset (Fin n))

-- Family is an antichain: no element is a subset of a different element
def Antichain {n : ℕ} (F : Family n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ A ⊆ B

-- Family has at least r elements for each size of an element in a family
def LevelRich (r : ℕ) {n : ℕ} (F : Family n) : Prop :=
  ∀ t ∈ F.image Finset.card, r ≤ (F.filter (fun A => A.card = t)).card

-- Family is both Antichain and LevelRich
def Valid (r : ℕ) {n : ℕ} (F : Family n) : Prop :=
  Antichain F ∧ LevelRich r F

-- Number of distinct element sizes
def numSizes {n : ℕ} (F : Family n) : ℕ :=
  (F.image Finset.card).card

-- Family is valid and has exactly n-3 distinct element sizes
def Achieves (r n : ℕ) : Prop :=
  ∃ F : Family n, Valid r F ∧ numSizes F + 3 = n

/-- The maximum number of distinct sizes in a valid family on `Fin n`. -/
noncomputable def g (n r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ F : Family n, Valid r F ∧ numSizes F = k}

/-- The maximum `g n r` is attained by a valid family, and bounds every valid family. -/
@[category test, AMS 5]
theorem test_g_is_max (n r : ℕ) :
    (∃ F : Family n, Valid r F ∧ numSizes F = g n r) ∧
      (∀ F : Family n, Valid r F → numSizes F ≤ g n r) := by
  classical
  let S : Set ℕ := {k | ∃ F : Family n, Valid r F ∧ numSizes F = k}
  have hne : S.Nonempty := by
    refine ⟨0, ∅, ?_, ?_⟩
    · simp [Valid, Antichain, LevelRich]
    · simp [numSizes]
  have hfin : S.Finite := by
    apply (Set.finite_range (fun F : Family n => numSizes F)).subset
    rintro k ⟨F, _, rfl⟩
    exact Set.mem_range_self F
  constructor
  · change g n r ∈ S
    unfold g
    exact hne.csSup_mem hfin
  · intro F hF
    change numSizes F ≤ sSup S
    exact le_csSup hfin.bddAbove ⟨F, hF, rfl⟩

section

set_option maxRecDepth 2000
/-- The first small case where mere existence of zero sizes differs from the maximum. -/
@[category test, AMS 5]
theorem test_g_r2_n3 : g 3 2 = 1 := by
  have hbound : ∀ F : Family 3, Valid 2 F → numSizes F ≤ 1 := by
    unfold Valid Antichain LevelRich numSizes
    decide
  obtain ⟨F, hF, hsize⟩ := (test_g_is_max 3 2).1
  have hle : g 3 2 ≤ 1 := by simpa [← hsize] using hbound F hF
  have hw : Valid 2 ({{0}, {1}} : Family 3) := by
    simp [Valid, Antichain, LevelRich, Finset.subset_iff]
    decide
  have hc : numSizes ({{0}, {1}} : Family 3) = 1 := by decide
  have hlow : 1 ≤ g 3 2 := by
    rw [← hc]
    exact (test_g_is_max 3 2).2 _ hw
  exact Nat.le_antisymm hle hlow

end

/-- `N` is a threshold when the maximum number of sizes is `n - 3` for every `n > N`.
The equation `g n r + 3 = n` also handles the small orders without truncated subtraction. -/
def IsThreshold (r N : ℕ) : Prop :=
  ∀ n > N, g n r + 3 = n

/-- The least eventual threshold for multiplicity `r`, provided a threshold exists. -/
noncomputable def n0 (r : ℕ) : ℕ :=
  sInf {N : ℕ | IsThreshold r N}

/-- For each `r ≥ 2`, some threshold exists. -/
@[category research solved, AMS 5]
theorem erdos_776.variants.threshold_exists (r : ℕ) (hr : 2 ≤ r) :
    ∃ N : ℕ, IsThreshold r N := by
  sorry

/-- The least threshold satisfies `n0(r) = 2r + o(r)` as `r` tends to infinity.
This is the asymptotic result of He and Tang (2026). -/
@[category research solved, AMS 5]
theorem erdos_776 :
    Tendsto (fun r : ℕ => (n0 r : ℝ) / (r : ℝ))
      atTop (nhds 2) := by
  sorry

/-- Does there exist an absolute constant $C > 0$ such that
$n_0(r) \leq 2r + C$ for all $r \geq 4$? [HeTa26, Problem 5.1] -/
@[category research open, question, AMS 5]
theorem erdos_776.variants.bounded_error :
    ∃ C : ℕ, ∀ r ≥ 4, n0 r ≤ 2 * r + C := by
  sorry

/-- Two singleton sets give the required one occurring size when `r = 2` and `n = 4`. -/
@[category test, AMS 5]
theorem test_r2_n4 : Achieves 2 4 := by
  refine ⟨{({0} : Finset (Fin 4)), ({1} : Finset (Fin 4))}, ?_, ?_⟩
  · simp [Valid, Antichain, LevelRich, Finset.subset_iff]
    decide
  · decide

/-- Three pairs and one singleton form an antichain, but the singleton level is too small. -/
@[category test, AMS 5]
theorem test_sparse_level_not_valid :
    ¬ Valid 3 ({{0,1},{0,2},{1,2},{3}} : Family 4) := by
  simp [Valid, Antichain, LevelRich, Finset.subset_iff]
  decide

/-- Both occurring levels have three sets, but the family contains comparable sets. -/
@[category test, AMS 5]
theorem test_containment_not_valid :
    ¬ Valid 3 ({{0},{1},{2},{0,1},{0,2},{1,2}} : Family 4) := by
  simp [Valid, Antichain, LevelRich, Finset.subset_iff]
  decide

/-- He and Tang (2026) proved that `n0(2) = 3`. -/
@[category research solved, AMS 5]
theorem erdos_776.variants.r2 :
    n0 2 = 3 := by
  sorry

/-- He and Tang (2026) proved that `n0(3) = 8`. -/
@[category research solved, AMS 5]
theorem erdos_776.variants.r3 :
    n0 3 = 8 := by
  sorry

/-- He and Tang (2026) lower bound for n0(r). -/
@[category research solved, AMS 5]
theorem erdos_776.variants.lower_bound
    (r : ℕ) (hr : 4 ≤ r) :
    2 * r + 2 ≤ n0 r := by
  sorry

/-- He and Tang's explicit upper bound
$n_0(r) \leq 2r + 2\log_2 r + \log_2\log_2 r + 15$ for $r \geq 2$ [HeTa26, (4.5)]. -/
@[category research solved, AMS 5]
theorem erdos_776.variants.upper_bound (r : ℕ) (hr : 2 ≤ r) :
    (n0 r : ℝ) ≤
      2 * (r : ℝ) + 2 * Real.logb 2 (r : ℝ) +
        Real.logb 2 (Real.logb 2 (r : ℝ)) + 15 := by
  sorry

end Erdos776
