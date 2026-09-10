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

public import FormalConjecturesForMathlib.Analysis.NormedSpace.WedgeCovectors
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Wedges of exact one-forms

Wedging the differentials of `p` scalar functions, all differentiated within one set, gives a
differential `p`-form on that set. This file proves it is closed, by identifying it with the
pullback of the constant volume form on `ℂ^p` along the map assembling the functions and applying
naturality of the exterior derivative.

Multiplying such a wedge by an analytic scalar therefore has exterior derivative the wedge of the
scalar's differential with it — the only case of the Leibniz rule the holomorphic de Rham complex
needs.
-/

@[expose] public noncomputable section

open ContinuousAlternatingMap
open scoped ContDiff

namespace DifferentialForm

/-- A wedge of derivatives is the pullback of the standard constant volume form. -/
lemma wedgeFDerivWithin_eq_standardVolumeForm_comp
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hf : ∀ i, DifferentiableWithinAt ℂ (f i) s x)
    (hs : UniqueDiffWithinAt ℂ s x) :
    wedgeCovectors E p (fun i ↦ fderivWithin ℂ (f i) s x) =
      (standardVolumeForm p).compContinuousLinearMap
        (fderivWithin ℂ (fun y i ↦ f i y) s x) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    standardVolumeForm, wedgeCovectors_apply_eq_det]
  congr 1
  ext i j
  rw [fderivWithin_pi hf hs]
  simp

/-- A wedge of differentials of scalar functions, all differentiated within the same set. -/
def exactWedgeWithin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) :
    E → E [⋀^Fin p]→L[ℂ] ℂ :=
  fun x ↦ wedgeCovectors E p (fun i ↦ fderivWithin ℂ (f i) s x)

/-- A wedge of exact one-forms is closed. The proof identifies it with the pullback of the
constant volume form and applies naturality of the exterior derivative. -/
lemma extDerivWithin_exactWedgeWithin_eq_zero
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hs : IsOpen s) (hx : x ∈ s)
    (hf : ∀ i, ContDiffOn ℂ ω (f i) s) :
    extDerivWithin (exactWedgeWithin E p f s) s x = 0 := by
  let F : E → (Fin p → ℂ) := fun y i ↦ f i y
  let η : (Fin p → ℂ) → (Fin p → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
    fun _ ↦ standardVolumeForm p
  have hF : ContDiffWithinAt ℂ ω F s x := contDiffWithinAt_pi.2 fun i ↦ hf i x hx
  have hEq : Set.EqOn (exactWedgeWithin E p f s)
      (fun y ↦ (η (F y)).compContinuousLinearMap
        (fderivWithin ℂ F s y)) s := by
    intro y hy
    exact wedgeFDerivWithin_eq_standardVolumeForm_comp E p f s y
      (fun i ↦ (hf i y hy).differentiableWithinAt (by simp))
      (hs.uniqueDiffWithinAt hy)
  rw [extDerivWithin_congr' hEq hx]
  rw [extDerivWithin_pullback
    (hω := differentiableAt_const (x := F x) (standardVolumeForm p) |>.differentiableWithinAt)
    (hf := hF) (hr := by simp) (hs := hs.uniqueDiffOn)
    (hxc := by simpa [hs.interior_eq] using (show x ∈ closure s from subset_closure hx))
    (hxs := hx) (hst := Set.mapsTo_univ F s)]
  have hη : extDerivWithin η Set.univ (F x) = 0 := by
    rw [extDerivWithin, show fderivWithin ℂ η Set.univ (F x) = 0 from
      congrFun (fderivWithin_const (𝕜 := ℂ) (E := Fin p → ℂ)
        (s := Set.univ) (standardVolumeForm p)) (F x)]
    exact map_zero _
  rw [hη]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma exactWedgeWithin_differentiableWithinAt
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hs : IsOpen s) (hx : x ∈ s)
    (hf : ∀ i, ContDiffOn ℂ ω (f i) s) :
    DifferentiableWithinAt ℂ (exactWedgeWithin E p f s) s x := by
  let F : E → (Fin p → ℂ) := fun y i ↦ f i y
  let η : (Fin p → ℂ) → (Fin p → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
    fun _ ↦ standardVolumeForm p
  have hF : ContDiffWithinAt ℂ ω F s x := contDiffWithinAt_pi.2 fun i ↦ hf i x hx
  have hDF : DifferentiableWithinAt ℂ (fderivWithin ℂ F s) s x :=
    (hF.fderivWithin_right (m := 1) hs.uniqueDiffOn (by simp) hx).differentiableWithinAt
      one_ne_zero
  have hPull : DifferentiableWithinAt ℂ
      (fun y ↦ (η (F y)).compContinuousLinearMap (fderivWithin ℂ F s y)) s x :=
    DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
      (differentiableWithinAt_const (c := standardVolumeForm p)) hDF
  apply hPull.congr
  · intro y hy
    exact wedgeFDerivWithin_eq_standardVolumeForm_comp E p f s y
      (fun i ↦ (hf i y hy).differentiableWithinAt (by simp))
      (hs.uniqueDiffWithinAt hy)
  · exact wedgeFDerivWithin_eq_standardVolumeForm_comp E p f s x
      (fun i ↦ (hf i x hx).differentiableWithinAt (by simp))
      (hs.uniqueDiffWithinAt hx)

/-- Exterior differentiation of `a · df₁ ∧ ⋯ ∧ dfₚ` gives
`da ∧ df₁ ∧ ⋯ ∧ dfₚ`. -/
lemma extDerivWithin_smul_exactWedgeWithin
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (a : E → ℂ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hs : IsOpen s) (hx : x ∈ s) (ha : ContDiffOn ℂ ω a s)
    (hf : ∀ i, ContDiffOn ℂ ω (f i) s) :
    extDerivWithin (fun y ↦ a y • exactWedgeWithin E p f s y) s x =
      wedgeCovectors E (p + 1)
        (Fin.cases (fderivWithin ℂ a s x)
          (fun i ↦ fderivWithin ℂ (f i) s x)) := by
  rw [extDerivWithin, fderivWithin_fun_smul
    (hs.uniqueDiffWithinAt hx)
    ((ha x hx).differentiableWithinAt (by simp))
    (exactWedgeWithin_differentiableWithinAt E p f s x hs hx hf),
    ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
  change a x • extDerivWithin (exactWedgeWithin E p f s) s x + _ = _
  rw [extDerivWithin_exactWedgeWithin_eq_zero E p f s x hs hx hf, smul_zero, zero_add]
  simp [exactWedgeWithin, wedgeCovectors]

end DifferentialForm
