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

public import FormalConjecturesForMathlib.AlgebraicGeometry.Points
public import Mathlib.AlgebraicGeometry.AffineSpace

import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Complex points of affine space

The complex points of algebraic affine space are canonically homeomorphic to tuples of complex
numbers. The proof identifies global regular functions with multivariate polynomials. It then uses
the localization description of sections on principal opens to handle every local regular function
appearing in the analytic topology.
-/

@[expose] public section

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexPoint

open Point

noncomputable section

/-- Evaluation of a global section at a complex point is pullback of that section to `Spec ℂ`. -/
lemma evaluate_top_eq_appTop {X : Over (Spec ↧ℂ)}
    (s : Γ(X.left, ⊤)) (z : ComplexPoint X) :
    evaluate ⊤ s z = (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop s) := by
  rw [evaluate, dif_pos (by exact trivial)]
  have h := Scheme.germ_stalkClosedPointTo (R := ↧ℂ) (X := X.left) z.left ⊤ trivial
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) s

/-- Evaluation of a global regular function is continuous in the analytic topology. -/
lemma continuous_evaluate_top {X : Over (Spec ↧ℂ)}
    (s : Γ(X.left, ⊤)) :
    @Continuous (ComplexPoint X) ℂ analyticTopology inferInstance
      (evaluate ⊤ s) := by
  rw [continuous_def]
  intro V hV
  simpa [overOpen] using
    isOpen_overOpen_inter_preimage (X := X) (⊤ : X.left.Opens) s V hV

/-- Complex affine space as a scheme over `Spec ℂ`. -/
abbrev complexAffineSpace (n : Type) : Scheme :=
  AffineSpace n (Spec ↧ℂ)

/-- Algebraic coordinates identify complex points of affine space with tuples of complex numbers. -/
def affineSpaceEquiv (n : Type) :
    ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)) ≃ (n → ℂ) where
  toFun z i :=
    (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop (AffineSpace.coord (Spec ↧ℂ) i))
  invFun v :=
    Over.homMk (AffineSpace.homOfVector (𝟙 _)
      (fun i ↦ (Scheme.ΓSpecIso ↧ℂ).inv (v i))) (by simp)
  left_inv z := by
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · simpa using (Over.w z).symm
    · intro i
      simp
  right_inv v := by
    funext i
    simp

@[simp]
lemma affineSpaceEquiv_apply (n : Type)
    (z : ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ))) (i : n) :
    affineSpaceEquiv n z i =
      (Scheme.ΓSpecIso ↧ℂ).hom
        (z.left.appTop (AffineSpace.coord (Spec ↧ℂ) i)) :=
  rfl

/-- The algebraic coordinate equivalence is continuous for the analytic topology. -/
lemma continuous_affineSpaceEquiv (n : Type) :
    @Continuous
      (ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)))
      (n → ℂ) analyticTopology inferInstance (affineSpaceEquiv n) := by
  apply @continuous_pi
    (ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)))
    n (fun _ ↦ ℂ) analyticTopology (fun _ ↦ inferInstance) (affineSpaceEquiv n)
  intro i
  let s := AffineSpace.coord (Spec ↧ℂ) i
  have heq : (fun z : ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)) ↦
      affineSpaceEquiv n z i) = evaluate ⊤ s :=
    funext fun z ↦ (evaluate_top_eq_appTop s z).symm
  rw [heq]
  exact continuous_evaluate_top (X := Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)) s

/-- The polynomial represented by a global regular function on complex affine space. -/
def affineGlobalPolynomial {n : Type} (s : Γ(complexAffineSpace n, ⊤)) :
    MvPolynomial n ℂ :=
  (Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).hom
    ((AffineSpace.SpecIso n ↧ℂ).inv.appTop s)

lemma SpecIso_hom_appTop_affineGlobalPolynomial {n : Type}
    (s : Γ(complexAffineSpace n, ⊤)) :
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop
        ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (affineGlobalPolynomial s)) = s := by
  rw [affineGlobalPolynomial, Iso.hom_inv_id_apply]
  change ((AffineSpace.SpecIso n ↧ℂ).inv.appTop ≫
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop) s = s
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

lemma SpecIso_hom_appTop_X {n : Type} (i : n) :
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop
        ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.X i)) =
      AffineSpace.coord (Spec ↧ℂ) i := by
  rw [← AffineSpace.SpecIso_inv_appTop_coord ↧ℂ i]
  change ((AffineSpace.SpecIso n ↧ℂ).inv.appTop ≫
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop)
      (AffineSpace.coord (Spec ↧ℂ) i) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

lemma SpecIso_hom_appTop_C {n : Type} (c : ℂ) :
    (AffineSpace.SpecIso n ↧ℂ).hom.appTop
        ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.C c)) =
      (complexAffineSpace n ↘ Spec ↧ℂ).appTop
        ((Scheme.ΓSpecIso ↧ℂ).inv c) := by
  rw [AffineSpace.SpecIso_hom_appTop]
  simp

/-- In affine coordinates, evaluation of a global section is evaluation of its polynomial. -/
lemma evaluate_affineSpaceEquiv_symm_top {n : Type} (s : Γ(complexAffineSpace n, ⊤))
    (v : n → ℂ) :
    evaluate ⊤ s ((affineSpaceEquiv n).symm v) =
      MvPolynomial.eval v (affineGlobalPolynomial s) := by
  rw [evaluate_top_eq_appTop]
  let h := ((affineSpaceEquiv n).symm v).left
  let φ : MvPolynomial n ℂ →+* ℂ :=
    ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv ≫
      (AffineSpace.SpecIso n ↧ℂ).hom.appTop ≫ h.appTop ≫
      (Scheme.ΓSpecIso ↧ℂ).hom).hom
  have hφ : φ = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro c
      dsimp [φ]
      rw [MvPolynomial.eval_C]
      change (Scheme.ΓSpecIso ↧ℂ).hom
        (h.appTop ((AffineSpace.SpecIso n ↧ℂ).hom.appTop
          ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.C c)))) = c
      rw [SpecIso_hom_appTop_C]
      change (Scheme.ΓSpecIso ↧ℂ).hom
        (((complexAffineSpace n ↘ Spec ↧ℂ).appTop ≫
          (AffineSpace.homOfVector (𝟙 _) fun i ↦
            (Scheme.ΓSpecIso ↧ℂ).inv (v i)).appTop)
              ((Scheme.ΓSpecIso ↧ℂ).inv c)) = c
      rw [← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over, Scheme.Hom.id_appTop]
      simp
    · intro i
      dsimp [φ]
      rw [MvPolynomial.eval_X]
      change (Scheme.ΓSpecIso ↧ℂ).hom
        (h.appTop ((AffineSpace.SpecIso n ↧ℂ).hom.appTop
          ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv (MvPolynomial.X i)))) = v i
      rw [SpecIso_hom_appTop_X]
      simp [h, affineSpaceEquiv]
  calc
    (Scheme.ΓSpecIso ↧ℂ).hom (h.appTop s) =
        (Scheme.ΓSpecIso ↧ℂ).hom
          (h.appTop ((AffineSpace.SpecIso n ↧ℂ).hom.appTop
            ((Scheme.ΓSpecIso ↧(MvPolynomial n ℂ)).inv
              (affineGlobalPolynomial s)))) := by
                rw [SpecIso_hom_appTop_affineGlobalPolynomial]
    _ = φ (affineGlobalPolynomial s) := rfl
    _ = MvPolynomial.eval v (affineGlobalPolynomial s) := by rw [hφ]

/-- Pullback of a global affine regular function along the coordinate inverse is continuous. -/
lemma continuous_evaluate_top_affineSpaceEquiv_symm {n : Type}
    (s : Γ(complexAffineSpace n, ⊤)) :
    Continuous fun v : n → ℂ ↦ evaluate ⊤ s ((affineSpaceEquiv n).symm v) := by
  simpa only [evaluate_affineSpaceEquiv_symm_top] using
    (affineGlobalPolynomial s).continuous_eval

/-- Principal opens of complex affine space pull back to Euclidean open sets. -/
lemma isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen {n : Type}
    (s : Γ(complexAffineSpace n, ⊤)) :
    IsOpen ((affineSpaceEquiv n).symm ⁻¹'
      overOpen ((complexAffineSpace n).basicOpen s)) := by
  rw [show (affineSpaceEquiv n).symm ⁻¹'
      overOpen ((complexAffineSpace n).basicOpen s) =
      {v | evaluate ⊤ s ((affineSpaceEquiv n).symm v) ≠ 0} by
    ext v
    exact mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)) (U := ⊤) s _ trivial]
  exact isOpen_ne_fun (continuous_evaluate_top_affineSpaceEquiv_symm s) continuous_const

/-- Evaluation on a principal open is continuous on the corresponding Euclidean open set. -/
lemma continuousOn_evaluate_basicOpen_affineSpaceEquiv_symm {n : Type}
    (f : Γ(complexAffineSpace n, ⊤))
    (t : Γ(complexAffineSpace n, (complexAffineSpace n).basicOpen f)) :
    ContinuousOn
      (fun v : n → ℂ ↦ evaluate ((complexAffineSpace n).basicOpen f) t
        ((affineSpaceEquiv n).symm v))
      ((affineSpaceEquiv n).symm ⁻¹'
        overOpen ((complexAffineSpace n).basicOpen f)) := by
  obtain ⟨k, a, h⟩ :=
    exists_evaluate_basicOpen_eq_div (X := Over.mk (complexAffineSpace n ↘ Spec ↧ℂ))
      (isAffineOpen_top (complexAffineSpace n)) f t
  have ha := continuous_evaluate_top_affineSpaceEquiv_symm a
  have hf := continuous_evaluate_top_affineSpaceEquiv_symm f
  have hrat : ContinuousOn
      (fun v : n → ℂ ↦ evaluate ⊤ a ((affineSpaceEquiv n).symm v) /
        evaluate ⊤ f ((affineSpaceEquiv n).symm v) ^ k)
      ((affineSpaceEquiv n).symm ⁻¹'
        overOpen ((complexAffineSpace n).basicOpen f)) :=
    ha.continuousOn.div (hf.pow k).continuousOn fun v hv ↦
      pow_ne_zero k ((mem_overOpen_basicOpen_iff_evaluate_ne_zero
        (X := Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)) (U := ⊤) f _ trivial).mp hv)
  exact hrat.congr fun v hv ↦ h _ hv

/-- The inverse coordinate map is continuous for every local regular-function subbasis set. -/
lemma continuous_affineSpaceEquiv_symm (n : Type) :
    @Continuous (n → ℂ)
      (ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)))
      inferInstance analyticTopology (affineSpaceEquiv n).symm := by
  rw [continuous_iff_analyticSubbasis]
  rintro W ⟨U, s, V, hV, rfl⟩
  rw [Set.preimage_inter, Set.preimage_preimage]
  apply isOpen_iff_forall_mem_open.mpr
  rintro v ⟨hvU, hvV⟩
  obtain ⟨f, hfU, hvf⟩ :=
    (isAffineOpen_top (complexAffineSpace n)).exists_basicOpen_le
      ⟨((affineSpaceEquiv n).symm v).underlying, hvU⟩ trivial
  let t := (complexAffineSpace n).presheaf.map (homOfLE hfU).op s
  let N := (affineSpaceEquiv n).symm ⁻¹'
      overOpen ((complexAffineSpace n).basicOpen f) ∩
    (fun w : n → ℂ ↦ evaluate ((complexAffineSpace n).basicOpen f) t
      ((affineSpaceEquiv n).symm w)) ⁻¹' V
  have hNopen : IsOpen N :=
    (continuousOn_evaluate_basicOpen_affineSpaceEquiv_symm f t).isOpen_inter_preimage
      (isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f) hV
  refine ⟨N, ?_, hNopen, ?_⟩
  · rintro w ⟨hwf, hwV⟩
    have hwU : (affineSpaceEquiv n).symm w ∈ overOpen U := hfU hwf
    refine ⟨hwU, ?_⟩
    change evaluate U s ((affineSpaceEquiv n).symm w) ∈ V
    rw [evaluate_res hfU s _ hwf]
    exact hwV
  · refine ⟨hvf, ?_⟩
    change evaluate ((complexAffineSpace n).basicOpen f) t
      ((affineSpaceEquiv n).symm v) ∈ V
    exact (congrArg (fun c ↦ c ∈ V) (evaluate_res hfU s _ hvf)).mp hvV

/-- The analytic topology on complex affine space. -/
noncomputable instance affineSpaceTopology (n : Type) :
    TopologicalSpace
      (ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ))) :=
  analyticTopology

/-- Complex affine space with the evaluation topology is ordinary complex affine space. -/
def affineSpaceHomeomorph (n : Type) :
    ComplexPoint (Over.mk (complexAffineSpace n ↘ Spec ↧ℂ)) ≃ₜ (n → ℂ) where
  toEquiv := affineSpaceEquiv n
  continuous_toFun := continuous_affineSpaceEquiv n
  continuous_invFun := continuous_affineSpaceEquiv_symm n

end


end AlgebraicGeometry.ComplexPoint
