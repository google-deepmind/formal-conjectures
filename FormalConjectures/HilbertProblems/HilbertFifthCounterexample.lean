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
    split_ifs with h₁ h₂
    all_goals simp_all
    all_goals linarith
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
  toFun x := WithLp.toLp 2 fun _ => x
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
      (x := Multiplicative.ofAdd 0)
  rw [contMDiffAt_iff] at hinv
  have hdiff := hinv.2.differentiableWithinAt (by simp)
  rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at hdiff
  simp only [mfld_simps] at hdiff
  let groupInv : Multiplicative ℝ → Multiplicative ℝ := fun a ↦ a⁻¹
  change DifferentiableAt ℝ
    (⇑badChart ∘
      groupInv ∘
      ↑(Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (⇑badChart) badChartedSpace._proof_1).symm)
    (badChart (Multiplicative.ofAdd 0)) at hdiff
  have hbase :
      badChart (Multiplicative.ofAdd 0) = realToEuclideanOne 0 := by
    change badChart (0 : ℝ) = realToEuclideanOne 0
    ext i
    fin_cases i
    simp [badChart, twistHomeomorph, twist, realToEuclideanOne]
  rw [hbase] at hdiff
  have hrealToEuclideanOne : DifferentiableAt ℝ realToEuclideanOne 0 := by
    change DifferentiableAt ℝ
      (fun x : ℝ ↦ WithLp.toLp 2 fun _ : Fin 1 ↦ x) 0
    apply (PiLp.hasFDerivAt_toLp 2 (fun _ : Fin 1 ↦ (0 : ℝ))).differentiableAt.comp 0
    fun_prop
  have hcoord := hdiff.comp 0 hrealToEuclideanOne
  have heval :
      DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0)
        (((⇑badChart ∘
          groupInv ∘
          ↑(Topology.IsOpenEmbedding.toOpenPartialHomeomorph
            (⇑badChart) badChartedSpace._proof_1).symm) ∘
          realToEuclideanOne) 0) :=
    (PiLp.hasFDerivAt_apply 2 _ 0).differentiableAt
  have hscalar := heval.fun_comp' 0 hcoord
  let scalarInv : ℝ → ℝ := fun x ↦
    (((⇑badChart ∘
          groupInv ∘
          ↑(Topology.IsOpenEmbedding.toOpenPartialHomeomorph
            (⇑badChart) badChartedSpace._proof_1).symm) ∘
        realToEuclideanOne) x) 0
  change DifferentiableAt ℝ scalarInv 0 at hscalar
  have hchart (x : ℝ) :
      badChart (untwist x) = realToEuclideanOne x := by
    simpa only [badChart, Homeomorph.trans_apply] using
      congrArg realToEuclideanOne (twistHomeomorph.apply_symm_apply x)
  have hinvChart (x : ℝ) :
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (⇑badChart) badChartedSpace._proof_1).symm (realToEuclideanOne x) = untwist x := by
    rw [← hchart x]
    exact badChart.isOpenEmbedding.toOpenPartialHomeomorph_left_inv
  have hscalarInv (x : ℝ) : scalarInv x = twist (-untwist x) := by
    simp only [scalarInv, Function.comp_apply]
    rw [hinvChart x]
    rfl
  have hkink : DifferentiableAt ℝ (fun x ↦ twist (-untwist x)) 0 :=
    hscalar.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun x ↦ (hscalarInv x).symm
  have hlinear : DifferentiableAt ℝ (fun x : ℝ ↦ (5 / 4 : ℝ) * x) 0 := by
    fun_prop
  have hrecover :=
    (hkink.add hlinear).const_mul (-4 / 3 : ℝ)
  have hrecover_eq (x : ℝ) :
      (-4 / 3 : ℝ) * (twist (-untwist x) + (5 / 4 : ℝ) * x) = |x| := by
    by_cases hx : 0 ≤ x
    · rcases hx.eq_or_lt with rfl | hxpos
      · norm_num [twist, untwist]
      · have hneg : ¬0 ≤ -x := by linarith
        rw [untwist, if_pos hx, twist, if_neg hneg, abs_of_pos hxpos]
        ring
    · have hxneg : x < 0 := lt_of_not_ge hx
      have hpos : 0 ≤ -(x / 2) := by linarith
      rw [untwist, if_neg hx, twist, if_pos hpos, abs_of_neg hxneg]
      ring
  have habs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 :=
    hrecover.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x ↦ (hrecover_eq x).symm
  exact not_differentiableAt_abs_zero habs

end

end Counterexample

end Hilbert5
