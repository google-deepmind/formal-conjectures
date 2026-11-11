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

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Interval discrepancy
-/

@[expose] public section

namespace Discrepancy

/-- Signed interval discrepancy of a finite family of real points. -/
noncomputable def interval (z : ℕ → ℝ) (I : Finset ℕ) (a b : ℝ) : ℝ :=
  ((I.filter fun n ↦ z n ∈ Set.Ico a b).card : ℝ) - (b - a) * I.card

/-- The supremum of the absolute discrepancies over half-open subintervals of `[0,1]`. -/
noncomputable def intervalSup (z : ℕ → ℝ) (I : Finset ℕ) : ℝ :=
  sSup {t | ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ t = |interval z I a b|}

/-- An empty sample has zero signed discrepancy. -/
@[simp] theorem interval_empty (z : ℕ → ℝ) (a b : ℝ) : interval z ∅ a b = 0 := by
  simp [interval]

/-- Interval discrepancy is bounded by the number of sampled points. -/
theorem abs_interval_le_card (z : ℕ → ℝ) (I : Finset ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : |interval z I a b| ≤ I.card := by
  have hcard : ((I.filter fun n ↦ z n ∈ Set.Ico a b).card : ℝ) ≤ I.card := by
    exact_mod_cast Finset.card_filter_le I (fun n ↦ z n ∈ Set.Ico a b)
  have hnonneg : (0 : ℝ) ≤ (I.filter fun n ↦ z n ∈ Set.Ico a b).card := by positivity
  have hsize : (0 : ℝ) ≤ I.card := by positivity
  unfold interval
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The supremum discrepancy is bounded by sample size, including the empty sample. -/
theorem intervalSup_le_card (z : ℕ → ℝ) (I : Finset ℕ) : intervalSup z I ≤ I.card := by
  apply csSup_le
  · refine ⟨0, 0, 0, le_rfl, le_rfl, zero_le_one, ?_⟩
    simp [interval]
  · rintro t ⟨a, b, ha, hab, hb, rfl⟩
    exact abs_interval_le_card z I ha hab hb

end Discrepancy
