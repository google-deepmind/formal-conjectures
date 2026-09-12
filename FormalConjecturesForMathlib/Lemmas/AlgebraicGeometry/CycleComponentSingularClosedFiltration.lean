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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSingularClosedFiltration

/-!
# Actual ambient closed supports for singular-component localization induction

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSingularClosedFiltration`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)

theorem cycleComponentSingularClosedFiltration_length :
    cycleComponentSingularClosedFiltration X x (cycleComponentSingularFiltrationLength X x) = ⊥ := by
  let := cycleComponent_isNoetherian X x
  exact reducedSmoothClosedFiltration_length _ _

omit [IsIntegral X.left] [Smooth X.hom] in
theorem cycleComponentSingularAmbientClosedFiltration_antitone :
    Antitone (cycleComponentSingularAmbientClosedFiltration X x) :=
  fun _ _ hkl ↦ Set.image_mono (reducedSmoothClosedFiltration_antitone _ _ hkl)

theorem cycleComponentSingularAmbientClosedFiltration_length :
    cycleComponentSingularAmbientClosedFiltration X x (cycleComponentSingularFiltrationLength X x) =
      ⊥ := by
  apply SetLike.coe_injective
  change cycleComponentι X.left x ''
    (cycleComponentSingularClosedFiltration X x (cycleComponentSingularFiltrationLength X x) : Set _) = ∅
  rw [cycleComponentSingularClosedFiltration_length]
  exact Set.image_empty _

/-- Every closed remainder stays below the proved singular-boundary dimension bound. -/
theorem cycleComponentSingularClosedFiltration_dimension_lt
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (cycleComponentSingularClosedFiltration X x k) < (d - p : ℕ) :=
  (IsEmbedding.inclusion (reducedSmoothClosedFiltration_le _ _ k)).isInducing.topologicalKrullDim_le.trans_lt
    (topologicalKrullDim_cycleComponent_singularLocus_lt X x hx)

/-- Every actual smooth layer has strictly smaller dimension than the component. -/
theorem cycleComponentSingularFiltrationStratum_dimension_lt
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (cycleComponentSingularFiltrationStratum X x k) < (d - p : ℕ) :=
  (topologicalKrullDim_reducedClosedSmoothPiece_le _ le_rfl).trans_lt
    (cycleComponentSingularClosedFiltration_dimension_lt X x hx k)

/-- The normal codimension lower bound is realized on actual standard-smooth affine
neighborhoods of every stratum point, including strata of nonconstant dimension. -/
theorem cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < d - p ∧ p + 1 ≤ d - n ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((cycleComponentSingularFiltrationStratumι X x k ≫ X.hom).appLE ⊤ U (by simp)).hom := by
  obtain ⟨U, hU, hzU, n, hn, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)
      (cycleComponentSingularFiltrationStratum_dimension_lt X x (d := d) hx k) z
  exact ⟨U, hU, hzU, n, hn, by omega, hstd⟩

/-- The dimension bound supplies genuine smooth scheme morphisms of fixed local
dimension, ready for the actual normal-coordinate construction. -/
theorem cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
    {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < d - p ∧ p + 1 ≤ d - n ∧
        SmoothOfRelativeDimension n (U.ι ≫ cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  obtain ⟨U, hU, hzU, n, hn, hcodim, hstd⟩ :=
    cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge X x
      (d := d) hx k z
  exact ⟨U, hU, hzU, n, hn, hcodim,
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

namespace ComplexPoint

attribute [local instance] cycleComponentSingularClosedFiltrationAnalyticTopology

omit [IsIntegral X.left] [Smooth X.hom] in
theorem cycleComponentSingularAnalyticClosedFiltration_antitone :
    Antitone (cycleComponentSingularAnalyticClosedFiltration X x) :=
  fun _ _ hkl _ hz ↦ cycleComponentSingularAmbientClosedFiltration_antitone X x hkl hz

theorem cycleComponentSingularAnalyticClosedFiltration_length :
    cycleComponentSingularAnalyticClosedFiltration X x (cycleComponentSingularFiltrationLength X x) =
      ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹'
    (cycleComponentSingularAmbientClosedFiltration X x (cycleComponentSingularFiltrationLength X x) :
      Set X.left) = ∅
  rw [cycleComponentSingularAmbientClosedFiltration_length]
  exact Set.preimage_empty

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Each analytic successive difference is the actual complex-point image of its smooth
stratum, not a supplied support parametrization. -/
theorem cycleComponentSingularAnalyticClosedFiltration_layer (k : ℕ) :
    Set.range (Point.map (cycleComponentSingularFiltrationStratumOverι X x k)) =
      (cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint X)) \
        (cycleComponentSingularAnalyticClosedFiltration X x (k + 1) : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion X]
  change Point.underlying ⁻¹' Set.range (cycleComponentSingularFiltrationStratumι X x k) = _
  rw [cycleComponentSingularAmbientClosedFiltration_layer]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Inside the exact localization open, the stratum's actual closed-embedding image
is precisely the current analytic closed support restricted to that open. -/
theorem cycleComponentSingularStratumClosedLift_complexPoints_range (k : ℕ) :
    Set.range (Point.map (cycleComponentSingularStratumClosedLiftOver X x k)) =
      Point.map (openInclusion X (cycleComponentSingularStratumAmbientOpen X x k)) ⁻¹'
          (cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion]
  change (Point.underlying : ComplexPoint (cycleComponentSingularStratumAmbientOpenOver X x k) →
    (cycleComponentSingularStratumAmbientOpenOver X x k).left) ⁻¹'
      Set.range (cycleComponentSingularStratumClosedLift X x k) = _
  rw [range_cycleComponentSingularStratumClosedLift]
  rfl

/-- Removing the first closed boundary support from the full cycle support gives
exactly the complex points of the actual smooth locus of the integral component. -/
theorem cycleComponentSmoothLocus_complexPoints_range_eq_support_sdiff_boundary :
    Set.range (Point.map (cycleComponentSmoothLocusOverι X x)) =
      cycleComponentSupport X x \
        (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X)) := by
  have he : Set.range ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ cycleComponentι X.left x) =
      closure {x} \
        (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      ← range_cycleComponentι X.left x]
    change cycleComponentι X.left x '' ((cycleComponentι X.left x ≫ X.hom).smoothLocus : Set _) =
      Set.range (cycleComponentι X.left x) \
        cycleComponentι X.left x '' ((cycleComponentι X.left x ≫ X.hom).smoothLocus : Set _)ᶜ
    rw [Set.range_sdiff_image (cycleComponentι X.left x).isClosedEmbedding.injective, compl_compl]
  rw [range_map_of_isImmersion X]
  change Point.underlying ⁻¹'
    Set.range ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
      cycleComponentι X.left x) = _
  rw [he]
  rfl

end ComplexPoint
end AlgebraicGeometry
