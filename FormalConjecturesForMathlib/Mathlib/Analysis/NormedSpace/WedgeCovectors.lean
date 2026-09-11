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

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Wedge products of continuous covectors

The wedge of `p` continuous linear functionals on a complex normed space is the alternating
`p`-form whose value on a family of vectors is the determinant of the matrix of pairings. This
file builds it by iterated alternatizing uncurry, proves the determinant formula, and derives the
multilinearity and alternation properties in each covector slot.

On `ℂ^d` the coordinate projections wedge to the standard volume form, and every continuous
alternating `p`-form is a finite combination of wedges of coordinate projections. The coefficients
in that expansion are continuous linear functionals of the form, so a form depending analytically
on a parameter has analytic coefficients.
-/

@[expose] public noncomputable section

namespace ContinuousAlternatingMap

/-- The wedge of `p` continuous linear functionals, built by iterated alternatizing uncurry. -/
def wedgeCovectors (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    (p : ℕ) → (Fin p → E →L[ℂ] ℂ) → E [⋀^Fin p]→L[ℂ] ℂ
  | 0, _ => ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) 1
  | p + 1, L => ContinuousAlternatingMap.alternatizeUncurryFin
      (ContinuousLinearMap.smulRight (L 0) (wedgeCovectors E p (fun i => L i.succ)))

/-- Evaluation of a wedge of covectors is the determinant of their pairing matrix. -/
lemma wedgeCovectors_apply_eq_det (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (v : Fin p → E),
      wedgeCovectors E p L v = Matrix.det
        (Matrix.of (fun i j ↦ L i (v j))) := by
  intro p
  induction p with
  | zero =>
      intro L v
      simp [wedgeCovectors]
  | succ p ih =>
      intro L v
      rw [wedgeCovectors, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [ContinuousLinearMap.smulRight_apply, Matrix.of_apply,
        zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [ih, mul_assoc]
      congr 2

/-- The wedge construction is additive in each covector. -/
lemma wedgeCovectors_update_add (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) (a b : E →L[ℂ] ℂ) :
    wedgeCovectors E p (Function.update L i (a + b)) =
      wedgeCovectors E p (Function.update L i a) +
        wedgeCovectors E p (Function.update L i b) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [ContinuousAlternatingMap.add_apply]
  simp only [wedgeCovectors_apply_eq_det]
  let A : Matrix (Fin p) (Fin p) ℂ := Matrix.of (fun k j ↦ L k (v j))
  have hAdd : Matrix.of (fun k j ↦ (Function.update L i (a + b)) k (v j)) =
      A.updateRow i (fun j ↦ a (v j) + b (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  have ha : Matrix.of (fun k j ↦ (Function.update L i a) k (v j)) =
      A.updateRow i (fun j ↦ a (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  have hb : Matrix.of (fun k j ↦ (Function.update L i b) k (v j)) =
      A.updateRow i (fun j ↦ b (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  rw [hAdd, ha, hb]
  exact Matrix.det_updateRow_add A i _ _

/-- The wedge construction is homogeneous in each covector. -/
lemma wedgeCovectors_update_smul (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) (c : ℂ) (a : E →L[ℂ] ℂ) :
    wedgeCovectors E p (Function.update L i (c • a)) =
      c • wedgeCovectors E p (Function.update L i a) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [ContinuousAlternatingMap.smul_apply]
  simp only [wedgeCovectors_apply_eq_det]
  let A : Matrix (Fin p) (Fin p) ℂ := Matrix.of (fun k j ↦ L k (v j))
  have hsmul : Matrix.of (fun k j ↦ (Function.update L i (c • a)) k (v j)) =
      A.updateRow i (c • fun j ↦ a (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  have ha : Matrix.of (fun k j ↦ (Function.update L i a) k (v j)) =
      A.updateRow i (fun j ↦ a (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  rw [hsmul, ha, Matrix.det_updateRow_smul]
  simp

/-- A wedge with two equal covectors vanishes. -/
lemma wedgeCovectors_eq_zero_of_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i j : Fin p)
    (h : L i = L j) (hne : i ≠ j) :
    wedgeCovectors E p L = 0 := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det]
  apply Matrix.det_zero_of_row_eq hne
  ext k
  simp [h]

/-- A wedge containing the zero covector vanishes. -/
lemma wedgeCovectors_update_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) :
    wedgeCovectors E p (Function.update L i 0) = 0 := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det]
  refine Matrix.det_eq_zero_of_row_eq_zero i fun j ↦ ?_
  simp

/-- The standard constant volume form on `ℂ^p`. -/
def standardVolumeForm (p : ℕ) :
    (Fin p → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  wedgeCovectors (Fin p → ℂ) p
    (fun i ↦ ContinuousLinearMap.proj i)

/-- Wedges of covectors commute with pullback along a continuous linear map. -/
lemma wedgeCovectors_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ℕ) (L : Fin p → F →L[ℂ] ℂ) (T : E →L[ℂ] F) :
    wedgeCovectors E p (fun i ↦ (L i).comp T) =
      (wedgeCovectors F p L).compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    wedgeCovectors_apply_eq_det]
  rfl

lemma add_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℕ} (a b : F [⋀^Fin p]→L[ℂ] ℂ) (T : E →L[ℂ] F) :
    (a + b).compContinuousLinearMap T =
      a.compContinuousLinearMap T + b.compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma smul_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℕ} (c : ℂ) (a : F [⋀^Fin p]→L[ℂ] ℂ) (T : E →L[ℂ] F) :
    (c • a).compContinuousLinearMap T = c • a.compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]


/-- The product of a tuple of coordinate covectors. -/
def covectorProduct (d p : ℕ) (I : Fin p → Fin d) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin p) ℂ).compContinuousLinearMap
    (fun j ↦ ContinuousLinearMap.proj (I j))

@[simp] lemma covectorProduct_apply (d p : ℕ) (I : Fin p → Fin d)
    (v : Fin p → Fin d → ℂ) :
    covectorProduct d p I v = ∏ j, v j (I j) := by
  simp [covectorProduct, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

/-- A multilinear form on a finite product is the sum of its coordinate monomials. -/
lemma multilinear_eq_sum_covectorProduct (d p : ℕ)
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ) :
    A = ∑ I : Fin p → Fin d,
      A (fun j ↦ Pi.single (I j) 1) • covectorProduct d p I := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  change A.toMultilinearMap =
    ContinuousMultilinearMap.toMultilinearMapLinear
      (R' := ℂ) (∑ I : Fin p → Fin d,
        A (fun j ↦ Pi.single (I j) 1) • covectorProduct d p I)
  rw [_root_.map_sum]
  simp_rw [_root_.map_smul]
  refine Module.Basis.ext_multilinear (fun _ : Fin p ↦ Pi.basisFun ℂ (Fin d)) fun v ↦ ?_
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single v]
  · simp [Pi.basisFun_apply]
  · intro I hI hne
    change A (fun j ↦ Pi.single (I j) 1) *
      covectorProduct d p I (fun j ↦ Pi.basisFun ℂ (Fin d) (v j)) = 0
    rw [covectorProduct_apply]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hz : (Pi.basisFun ℂ (Fin d) (v j)) (I j) = 0 := by
      simp [Pi.basisFun_apply, hj.symm]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]
  · simp

/-- Alternatizing a coordinate monomial gives the wedge of its coordinate covectors. -/
lemma alternatization_covectorProduct (d p : ℕ) (I : Fin p → Fin d) :
    ContinuousMultilinearMap.alternatization (covectorProduct d p I) =
      wedgeCovectors (Fin d → ℂ) p (fun j ↦ ContinuousLinearMap.proj (I j)) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [ContinuousMultilinearMap.alternatization_apply_apply,
    wedgeCovectors_apply_eq_det, ← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [covectorProduct_apply]
  congr 1

lemma alternatization_smul (d p : ℕ) (c : ℂ)
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ) :
    ContinuousMultilinearMap.alternatization (c • M) =
      c • ContinuousMultilinearMap.alternatization M := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [ContinuousMultilinearMap.alternatization_apply_apply, _root_.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [smul_comm]

lemma alternatization_toContinuousMultilinearMap (d p : ℕ)
    (A : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :
    ContinuousMultilinearMap.alternatization A.toContinuousMultilinearMap =
      (p.factorial : ℂ) • A := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  change MultilinearMap.alternatization A.toAlternatingMap.toMultilinearMap =
    (p.factorial : ℂ) • A.toAlternatingMap
  simpa only [Fintype.card_fin, Nat.cast_smul_eq_nsmul] using
    AlternatingMap.coe_alternatization A.toAlternatingMap

/-- A continuous alternating form on `Fin d → ℂ` is the finite coordinate-wedge expansion
of its values on the standard coordinate vectors. -/
lemma alternating_eq_sum_wedgeCovectors (d p : ℕ)
    (A : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :
    A = ∑ I : Fin p → Fin d,
      ((p.factorial : ℂ)⁻¹ * A (fun j ↦ Pi.single (I j) 1)) •
        wedgeCovectors (Fin d → ℂ) p
          (fun j ↦ ContinuousLinearMap.proj (I j)) := by
  classical
  have hM := multilinear_eq_sum_covectorProduct d p A.toContinuousMultilinearMap
  have hAlt := congrArg ContinuousMultilinearMap.alternatization hM
  rw [alternatization_toContinuousMultilinearMap d p A] at hAlt
  simp only [_root_.map_sum] at hAlt
  simp_rw [alternatization_smul, alternatization_covectorProduct] at hAlt
  change (p.factorial : ℂ) • A =
    ∑ I : Fin p → Fin d, A (fun j ↦ Pi.single (I j) 1) •
      wedgeCovectors (Fin d → ℂ) p
        (fun j ↦ ContinuousLinearMap.proj (I j)) at hAlt
  have hfac : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  calc
    A = (p.factorial : ℂ)⁻¹ • ((p.factorial : ℂ) • A) := by
      rw [← mul_smul, inv_mul_cancel₀ hfac, one_smul]
    _ = (p.factorial : ℂ)⁻¹ • ∑ I : Fin p → Fin d,
        A (fun j ↦ Pi.single (I j) 1) •
          wedgeCovectors (Fin d → ℂ) p
            (fun j ↦ ContinuousLinearMap.proj (I j)) := by rw [hAlt]
    _ = _ := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun I _ ↦ smul_smul _ _ _

/-- Evaluation at a fixed tuple is a continuous linear functional on continuous alternating
forms. -/
def alternatingFormEvaluation (d p : ℕ) (v : Fin p → Fin d → ℂ) :
    ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  let L : ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun A ↦ A v
      map_add' := fun A B ↦ by simp
      map_smul' := fun a A ↦ by simp [ContinuousAlternatingMap.smul_apply] }
  LinearMap.mkContinuous L (∏ j, ‖v j‖) (fun A ↦ by
    change ‖A v‖ ≤ (∏ j, ‖v j‖) * ‖A‖
    simpa only [mul_comm] using A.le_opNorm v)

/-- The coefficient of an alternating form field in its finite coordinate-wedge expansion. -/
def coordinateCoefficient (d p : ℕ)
    (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (I : Fin p → Fin d) (y : Fin d → ℂ) : ℂ :=
  (p.factorial : ℂ)⁻¹ * θ y (fun j ↦ Pi.single (I j) 1)

lemma analyticOnNhd_coordinateCoefficient (d p : ℕ)
    (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    {s : Set (Fin d → ℂ)} (hθ : AnalyticOnNhd ℂ θ s) (I : Fin p → Fin d) :
    AnalyticOnNhd ℂ (coordinateCoefficient d p θ I) s := by
  let e : Fin p → Fin d → ℂ := fun j ↦ Pi.single (I j) 1
  exact ((alternatingFormEvaluation d p e).comp_analyticOnNhd hθ).const_smul
    (c := (p.factorial : ℂ)⁻¹)

end ContinuousAlternatingMap
