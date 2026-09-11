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

public import FormalConjecturesForMathlib.AlgebraicTopology.ComplexNeighborhoodOrientation
public import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClassDifferentiableInvariance

/-!
# Moving the center of a complex-coordinate embedding

For a continuous injective map `F : ℂ^d → ℂ^d`, the maps
`w ↦ F(w + t • v) - F(t • v)` form a homotopy of punctured pairs. Injectivity, not
differentiability at varying centers, prevents this homotopy from hitting zero.

In particular the standard radial chart compression preserves the exact complex local class
at every center. Complex differentiability is used only at the model origin, where the
derivative is a positive scalar times the identity. No assertion that radial compression is
holomorphic away from the origin is needed or made.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular

variable (d : ℕ)

/-- Recenter a continuous injection at a chosen source point. -/
def centeredComplexEmbeddingPair (F : (Fin d → ℂ) → (Fin d → ℂ))
    (hF : Continuous F) (hFi : Function.Injective F) (v : Fin d → ℂ) :
    standardComplexPuncturedPair d ⟶ standardComplexPuncturedPair d :=
  complexPuncturedPairMapOf d (fun w => F (w + v) - F v)
    ((hF.comp (continuous_id.add continuous_const)).sub continuous_const)
    (by simp) (fun w hw h => hw
      (add_right_cancel (show w + v = 0 + v by simpa using hFi (sub_eq_zero.mp h))))

/-- An explicit punctured-pair homotopy moving the center from zero to `v`. -/
def centeredComplexEmbeddingPairHomotopy (F : (Fin d → ℂ) → (Fin d → ℂ))
    (hF : Continuous F) (hFi : Function.Injective F) (v : Fin d → ℂ) :
    TopPair.Homotopy (centeredComplexEmbeddingPair d F hF hFi 0)
      (centeredComplexEmbeddingPair d F hF hFi v) where
  fst :=
    { toFun := fun tw : unitInterval × (Fin d → ℂ) =>
        F (tw.2 + (tw.1 : ℝ) • v) - F ((tw.1 : ℝ) • v)
      continuous_toFun := by fun_prop
      map_zero_left := fun w : Fin d → ℂ => by
        change F (w + (0 : ℝ) • v) - F ((0 : ℝ) • v) = F (w + 0) - F 0
        simp
      map_one_left := fun w : Fin d → ℂ => by
        change F (w + (1 : ℝ) • v) - F ((1 : ℝ) • v) = F (w + v) - F v
        simp }
  snd :=
    { toFun := fun tw => ⟨F (tw.2.1 + (tw.1 : ℝ) • v) - F ((tw.1 : ℝ) • v), by
        intro h
        apply tw.2.2
        exact add_right_cancel (show tw.2.1 + (tw.1 : ℝ) • v = 0 + (tw.1 : ℝ) • v by
          simpa using hFi (sub_eq_zero.mp h))⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun w => by
        apply Subtype.ext
        change F (w.1 + (0 : ℝ) • v) - F ((0 : ℝ) • v) = F (w.1 + 0) - F 0
        simp
      map_one_left := fun w => by
        apply Subtype.ext
        change F (w.1 + (1 : ℝ) • v) - F ((1 : ℝ) • v) = F (w.1 + v) - F v
        simp }
  w := rfl

/-- The homology action of an injective coordinate map is unchanged by moving its center. -/
theorem centeredComplexEmbeddingPair_relativeHomologyMap_eq
    (F : (Fin d → ℂ) → (Fin d → ℂ)) (hF : Continuous F) (hFi : Function.Injective F)
    (v : Fin d → ℂ) (n : ℕ) :
    relativeHomologyMap ℚ n (centeredComplexEmbeddingPair d F hF hFi v) =
      relativeHomologyMap ℚ n (centeredComplexEmbeddingPair d F hF hFi 0) :=
  ((centeredComplexEmbeddingPairHomotopy d F hF hFi v).congr_relativeHomologyMap n).symm

/-- Global continuity of the radial coordinate compression. -/
@[fun_prop]
lemma continuous_complexUnivBall (c : Fin d → ℂ) (r : ℝ) :
    Continuous (OpenPartialHomeomorph.univBall c r : (Fin d → ℂ) → (Fin d → ℂ)) :=
  ((OpenPartialHomeomorph.univBall c r).isOpenEmbedding
    (OpenPartialHomeomorph.univBall_source c r)).continuous

/-- Global injectivity of the radial coordinate compression. -/
lemma injective_complexUnivBall (c : Fin d → ℂ) (r : ℝ) :
    Function.Injective (OpenPartialHomeomorph.univBall c r :
      (Fin d → ℂ) → (Fin d → ℂ)) :=
  ((OpenPartialHomeomorph.univBall c r).isOpenEmbedding
    (OpenPartialHomeomorph.univBall_source c r)).injective

/-- At every center the positive-radius compression preserves the precisely normalized
complex local homology class. -/
theorem centeredComplexUnivBall_preserves_standardComplexLocalClass
    (c : Fin d → ℂ) (r : ℝ) (hr : 0 < r) (v : Fin d → ℂ) :
    relativeHomologyMap ℚ (2 * d)
      (centeredComplexEmbeddingPair d (OpenPartialHomeomorph.univBall c r)
        (continuous_complexUnivBall d c r) (injective_complexUnivBall d c r) v)
      (standardComplexLocalClass d) = standardComplexLocalClass d := by
  rw [centeredComplexEmbeddingPair_relativeHomologyMap_eq]
  let L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (r : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ)
  have hL : Function.Injective L := by
    intro w z hwz
    change (r : ℂ) • w = (r : ℂ) • z at hwz
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact (smul_right_injective _ hr') hwz
  let A := complexMatrixOfContinuousLinearMap d L
  have hA : A.det ≠ 0 := complexMatrixOfContinuousLinearMap_det_ne_zero d L hL
  have hAL : (A.mulVecLin.toContinuousLinearMap :
      (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = L :=
    ContinuousLinearMap.ext (complexMatrixOfContinuousLinearMap_mulVec d L)
  apply relativeHomologyMap_complexDifferentiable_standardComplexLocalClass d A hA
  rw [hAL]
  simpa only [add_zero] using
    (hasFDerivAt_univBall_complex d c r hr).sub_const
      ((OpenPartialHomeomorph.univBall c r) 0)

end AlgebraicTopology.Singular
