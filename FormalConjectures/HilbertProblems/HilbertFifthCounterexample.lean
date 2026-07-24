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
# Counterexample to the formulation of Hilbert's fifth problem

The formulation in `FormalConjectures.HilbertProblems.5` claims that the group operations are
analytic in any supplied topological atlas. This file proves `False` by applying that result to
the additive real line equipped with a chart having different slopes on the two sides of zero.
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

/-- The current formulation of Hilbert's fifth problem implies `False`. -/
@[category test, AMS 22]
theorem hilbert_fifth_problem_implies_false : False := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Multiplicative ℝ) := badChartedSpace
  have hinv :=
    (hilbert_fifth_problem (G := Multiplicative ℝ) (n := 1)).contMDiff_inv.contMDiffAt
      (x := (1 : Multiplicative ℝ))
  rw [contMDiffAt_iff] at hinv
  exact hinv

end

end Counterexample

end Hilbert5
