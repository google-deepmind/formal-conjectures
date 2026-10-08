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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-!
# Erdős Problem 223: diameter pairs

Source: supplied 223.pdf; https://www.erdosproblems.com/223.
Primary reference: K. J. Swanepoel, Unit distances and diameters in Euclidean
spaces, arXiv:0707.0213, Section 1.2 and Corollary 3.

The problem is SOLVED in the literature. This file proves foundational results
about its extremal function and the exact two-point case. It does NOT prove the
main planar, three-dimensional, asymptotic, or eventual exact formulas. Those
known results are explicitly recorded as propositions in `ResearchTargets`.
This is therefore a PARTIAL proof formalization, not a complete solution.

The quoted small-dimensional formulas require n >= 3 and n >= 4, respectively;
they are false at n = 2. Diameter pairs are unordered, distinct two-element
subsets. Euclidean diameter is exactly 1, not merely bounded by 1.
-/

/- Verified with Lean v4.35.0-rc3 and Mathlib commit
25730c7c759d108ef87ab70af2342a196760f79d (2026-10-01). -/

namespace Erdos223

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Two-element subsets at distance 1; each unordered pair is counted once. -/
noncomputable def unitPairs {d : ℕ} (A : Finset (Space d)) : Finset (Finset (Space d)) := by
  classical
  exact (A.powersetCard 2).filter fun B => Metric.diam (B : Set (Space d)) = 1

noncomputable def pairCount {d : ℕ} (A : Finset (Space d)) : ℕ := (unitPairs A).card

/-- The original admissible sets: exactly n points, with diameter exactly 1. -/
def Configuration (d n : ℕ) (A : Finset (Space d)) : Prop :=
  A.card = n ∧ Metric.diam (A : Set (Space d)) = 1

/-- Attainable numbers of diameter pairs. -/
def attainable (d n : ℕ) : Set ℕ :=
  {m | ∃ A : Finset (Space d), Configuration d n A ∧ pairCount A = m}

/-- Maximum number of diameter pairs; attainment is proved below for d >= 1, n >= 2. -/
noncomputable def extremal (d n : ℕ) : ℕ := sSup (attainable d n)

/-- The pair representation has the intended metric interpretation. -/
theorem pair_mem_iff {d : ℕ} {A : Finset (Space d)} {x y : Space d} (hxy : x ≠ y) :
    {x, y} ∈ unitPairs A ↔ x ∈ A ∧ y ∈ A ∧ dist x y = 1 := by
  classical
  simp [unitPairs, Finset.mem_powersetCard, hxy, Metric.diam_pair, Finset.insert_subset_iff, Finset.singleton_subset_iff, and_assoc]

/-- The elementary upper bound, independently of any diameter hypothesis. -/
theorem pairCount_le_choose {d : ℕ} (A : Finset (Space d)) :
    pairCount A ≤ A.card.choose 2 := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard 2 A)

theorem attainable_bddAbove (d n : ℕ) : BddAbove (attainable d n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨A, hA, rfl⟩
  simpa [hA.1] using pairCount_le_choose A

theorem attainable_finite (d n : ℕ) : (attainable d n).Finite :=
  (attainable_bddAbove d n).finite

/-- Every configuration gives a genuine lower bound on the extremal function. -/
theorem pairCount_le_extremal {d n : ℕ} {A : Finset (Space d)}
    (hA : Configuration d n A) : pairCount A ≤ extremal d n :=
  le_csSup (attainable_bddAbove d n) ⟨A, hA, rfl⟩

theorem extremal_le_choose (d n : ℕ) : extremal d n ≤ n.choose 2 := by
  apply csSup_le'
  rintro m ⟨A, hA, rfl⟩
  simpa [hA.1] using pairCount_le_choose A

/-- Embed the real line isometrically as the first coordinate axis. -/
noncomputable def axis {d : ℕ} (hd : 0 < d) (t : ℝ) : Space d :=
  PiLp.single 2 ⟨0, hd⟩ t

@[simp] theorem dist_axis {d : ℕ} (hd : 0 < d) (s t : ℝ) :
    dist (axis hd s) (axis hd t) = dist s t := by
  simp [axis]

theorem axis_injective {d : ℕ} (hd : 0 < d) : Function.Injective (axis hd) := by
  intro s t h
  apply dist_eq_zero.mp
  rw [← dist_axis hd, h, dist_self]

/-- Equally spaced points provide a configuration for every valid d and n. -/
theorem configuration_exists {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ A : Finset (Space d), Configuration d n A := by
  classical
  let q : ℕ → ℝ := fun i => (i : ℝ) / (n - 1 : ℕ)
  let p : ℕ → Space d := fun i => axis hd (q i)
  let A := (Finset.range n).image p
  have hnpos : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hpinj : Function.Injective p := by
    intro i j hij
    have heq := axis_injective hd hij
    have hcast : (i : ℝ) = (j : ℝ) := (div_left_inj' hnpos.ne').mp heq
    exact_mod_cast hcast
  have hq (i : ℕ) (hi : i < n) : 0 ≤ q i ∧ q i ≤ 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hnpos.le
    · apply (div_le_one hnpos).mpr
      exact_mod_cast (show i ≤ n - 1 by omega)
  have hbound : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1 := by
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hi' := hq i (Finset.mem_range.mp hi)
    have hj' := hq j (Finset.mem_range.mp hj)
    change dist (axis hd (q i)) (axis hd (q j)) ≤ 1
    rw [dist_axis, Real.dist_eq, abs_le]
    constructor <;> linarith
  have hzero : p 0 ∈ A := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  have hlast : p (n - 1) ∈ A :=
    Finset.mem_image.mpr ⟨n - 1, Finset.mem_range.mpr (by omega), rfl⟩
  have hdist : dist (p 0) (p (n - 1)) = 1 := by
    simp [p, q, hnpos.ne', Real.dist_eq]
  refine ⟨A, ?_, le_antisymm ?_ ?_⟩
  · simp [A, Finset.card_image_of_injective _ hpinj]
  · exact Metric.diam_le_of_forall_dist_le (by norm_num) hbound
  · rw [← hdist]
    exact Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hzero hlast

theorem attainable_nonempty {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n) :
    (attainable d n).Nonempty := by
  obtain ⟨A, hA⟩ := configuration_exists hd hn
  exact ⟨pairCount A, A, hA, rfl⟩

/-- The supremum is an attained maximum, not a formal default value. -/
theorem extremal_attained {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ A : Finset (Space d), Configuration d n A ∧ pairCount A = extremal d n :=
  (attainable_nonempty hd hn).csSup_mem (attainable_finite d n)

/-- Exact universal-property characterization of the maximum. -/
theorem extremal_eq_iff {d n m : ℕ} (hd : 0 < d) (hn : 2 ≤ n) :
    extremal d n = m ↔
      (∃ A : Finset (Space d), Configuration d n A ∧ pairCount A = m) ∧
      (∀ A : Finset (Space d), Configuration d n A → pairCount A ≤ m) := by
  constructor
  · intro h
    constructor
    · simpa [h] using extremal_attained hd hn
    · intro A hA
      simpa [h] using pairCount_le_extremal hA
  · rintro ⟨⟨A, hA, hm⟩, hub⟩
    apply le_antisymm
    · obtain ⟨B, hB, hmax⟩ := extremal_attained hd hn
      rw [← hmax]
      exact hub B hB
    · rw [← hm]
      exact pairCount_le_extremal hA

/-- A normalized two-point set has exactly one diameter pair. -/
theorem pairCount_two {d : ℕ} {A : Finset (Space d)} (hA : Configuration d 2 A) :
    pairCount A = 1 := by
  classical
  unfold pairCount unitPairs
  rw [← hA.1, Finset.powersetCard_self]
  rw [Finset.filter_singleton]
  simp only [hA.2, ite_true, Finset.card_singleton]

/-- Boundary case omitted by the summary formulas in the supplied PDF. -/
theorem extremal_two {d : ℕ} (hd : 0 < d) : extremal d 2 = 1 := by
  obtain ⟨A, hA, hmax⟩ := extremal_attained hd (by omega : 2 ≤ 2)
  rw [← hmax]
  exact pairCount_two hA

theorem planar_formula_fails_at_two : extremal 2 2 ≠ 2 := by
  rw [extremal_two (by decide)]
  decide

theorem spatial_formula_fails_at_two : extremal 3 2 ≠ 2 * 2 - 2 := by
  rw [extremal_two (by decide)]
  decide

/-- The spatial formula also fails at n = 3, even by the elementary pair bound. -/
theorem spatial_formula_fails_at_three : extremal 3 3 ≠ 2 * 3 - 2 := by
  have h := extremal_le_choose 3 3
  norm_num at h ⊢
  omega

/-! ## Known results whose proofs are not provided in this file -/
namespace ResearchTargets

/-- Hopf–Pannwitz, with the necessary small-n restriction. -/
def PlanarFormula : Prop := ∀ n : ℕ, 3 ≤ n → extremal 2 n = n

/-- Grünbaum–Heppes–Straszewicz, with the necessary small-n restriction. -/
def SpatialFormula : Prop := ∀ n : ℕ, 4 ≤ n → extremal 3 n = 2 * n - 2

/-- The real-valued coefficient; natural division is used only to form floor(d/2). -/
noncomputable def coefficient (d : ℕ) : ℝ :=
  (((d / 2 : ℕ) : ℝ) - 1) / (2 * ((d / 2 : ℕ) : ℝ))

/-- Erdős's asymptotic formula, separately for every fixed d >= 4. -/
def AsymptoticFormula : Prop :=
  ∀ d : ℕ, 4 ≤ d →
    Filter.Tendsto (fun n : ℕ => (extremal d n : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop (nhds (coefficient d))

/-- Ceiling(n / p) for natural inputs with p > 0 in every intended use. -/
def ceilDiv (n p : ℕ) : ℕ := (n + p - 1) / p

/-- Swanepoel's Corollary 3: the eventual exact values, counting edges in Mathlib's Turán graph. -/
def exactValue (d n : ℕ) : ℕ :=
  if d = 4 then
    (SimpleGraph.turanGraph n 2).edgeFinset.card + ceilDiv n 2 + (if n % 4 = 3 then 0 else 1)
  else if d = 5 then (SimpleGraph.turanGraph n 2).edgeFinset.card + n
  else if d % 2 = 0 then (SimpleGraph.turanGraph n (d / 2)).edgeFinset.card + d / 2
  else (SimpleGraph.turanGraph n (d / 2)).edgeFinset.card + ceilDiv n (d / 2) + d / 2 - 1

/-- The threshold can depend on dimension; no uniform threshold is claimed. -/
def EventualExactFormula : Prop :=
  ∀ d : ℕ, 4 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → extremal d n = exactValue d n

end ResearchTargets
end Erdos223
