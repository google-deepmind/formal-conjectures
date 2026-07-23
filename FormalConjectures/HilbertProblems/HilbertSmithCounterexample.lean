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

import FormalConjectures.HilbertProblems.«5»

/-!
# Counterexample to an overly strong formulation of Hilbert's fifth problem

Hilbert's fifth problem produces a compatible analytic atlas; it does not make an arbitrary
topological atlas analytic. This file equips the additive real line with a chart having different
slopes on the two sides of zero. In this chart, inversion has different one-sided derivatives at
the identity, contradicting the conclusion that it is analytic.
-/

open scoped Manifold ContDiff EuclideanGeometry

namespace Hilbert5

namespace Counterexample

noncomputable section

private def twist (x : ℝ) : ℝ := if 0 ≤ x then x else 2 * x

private def untwist (x : ℝ) : ℝ := if 0 ≤ x then x else x / 2

private def twistHomeomorph : ℝ ≃ₜ ℝ where
  toFun := twist
  invFun := untwist
  left_inv x := by
    simp only [twist, untwist]
    split_ifs with h₁ h₂ <;> simp_all <;> linarith
  right_inv x := by
    simp only [twist, untwist]
    split_ifs with h₁ h₂ <;> simp_all <;> linarith
  continuous_toFun := by
    apply Continuous.if_le continuous_id (continuous_const.mul continuous_id)
        continuous_const continuous_id
    intro x hx
    simp only [id_eq] at hx ⊢
    subst x
    ring
  continuous_invFun := by
    apply Continuous.if_le continuous_id (continuous_id.div_const 2)
        continuous_const continuous_id
    intro x hx
    simp only [id_eq] at hx ⊢
    subst x
    ring

private def realToEuclideanOne : ℝ ≃ₜ EuclideanSpace ℝ (Fin 1) where
  toFun x := PiLp.toLp 2 fun _ => x
  invFun x := x 0
  left_inv x := by simp
  right_inv x := by
    ext i
    fin_cases i
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def badChart : ℝ ≃ₜ EuclideanSpace ℝ (Fin 1) :=
  twistHomeomorph.trans realToEuclideanOne

private def badChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ℝ :=
  badChart.isOpenEmbedding.singletonChartedSpace

/-- The former formulation of Hilbert's fifth problem, which asserted that the group operations
are analytic in any supplied topological atlas, implies `False`. -/
@[category test, AMS 22]
theorem old_hilbert_fifth_is_false
    (old_hilbert_fifth :
      ∀ (G : Type) [Group G] [TopologicalSpace G] (n : ℕ)
        [IsTopologicalGroup G] [ChartedSpace (EuclideanSpace ℝ (Fin n)) G],
        LieGroup (𝓡 n) ω G) :
    False := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Multiplicative ℝ) := badChartedSpace
  have hLie : LieGroup (𝓡 1) ω (Multiplicative ℝ) :=
    old_hilbert_fifth (Multiplicative ℝ) 1
  have hinv := hLie.contMDiff_inv.contMDiffAt (x := (1 : Multiplicative ℝ))
  rw [contMDiffAt_iff] at hinv
  exact hinv

end

end Counterexample

end Hilbert5
