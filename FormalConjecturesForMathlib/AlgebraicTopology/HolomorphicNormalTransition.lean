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

public import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClassDifferentiableInvariance
public import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClassGenerator
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The normal derivative of a support-preserving holomorphic transition

Preservation of the zero-normal plane forces the tangent-to-normal derivative block to
vanish. Differentiating the actual local inverse identity then constructs inverse normal
blocks. No invertibility or orientation-preservation theorem is supplied for the normal
map; both are consequences of the given holomorphic support-preserving coordinate transition.
-/

@[expose] public noncomputable section

open Topology Filter CategoryTheory

namespace AlgebraicTopology.Singular

section GeneralNormal

variable {E N : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup N] [NormedSpace ℂ N]

/-- The normal-to-normal block of an actual ambient derivative. -/
def normalBlock (A : (E × N) →L[ℂ] (E × N)) : N →L[ℂ] N :=
  (ContinuousLinearMap.snd ℂ E N).comp (A.comp (ContinuousLinearMap.inr ℂ E N))

@[simp] theorem normalBlock_apply (A : (E × N) →L[ℂ] (E × N)) (v : N) :
    normalBlock A v = (A (0, v)).2 := rfl

/-- Differentiating preservation of the zero-normal plane kills the mixed derivative. -/
theorem normal_tangent_derivative_eq_zero {f : (E × N) → (E × N)}
    {A : (E × N) →L[ℂ] (E × N)} {a : E}
    (hf : HasFDerivAt f A (a, 0))
    (hplane : ∀ᶠ v in 𝓝 a, (f (v, 0)).2 = 0) (v : E) : (A (v, 0)).2 = 0 := by
  have hc := (ContinuousLinearMap.snd ℂ E N).hasFDerivAt.comp a
    (hf.comp a (ContinuousLinearMap.inl ℂ E N).hasFDerivAt)
  have hp : (fun v : E => (f (v, 0)).2) =ᶠ[𝓝 a] fun _ => (0 : N) := hplane
  have heq := (hc.congr_of_eventuallyEq hp.symm).unique (hasFDerivAt_const (0 : N) a)
  exact DFunLike.congr_fun heq v

/-- The normal blocks inherit an actual left inverse from a split ambient derivative
when the inverse derivative preserves the tangent plane. -/
theorem normalBlock_leftInverse (A B : (E × N) →L[ℂ] (E × N))
    (hBA : B.comp A = ContinuousLinearMap.id ℂ (E × N))
    (hBT : ∀ v : E, (B (v, 0)).2 = 0) :
    Function.LeftInverse (normalBlock B) (normalBlock A) := by
  intro v
  have h := congrArg Prod.snd (DFunLike.congr_fun hBA (0, v))
  have hs : A (0, v) = ((A (0, v)).1, 0) + (0, (A (0, v)).2) := by simp
  change (B (A (0, v))).2 = v at h
  rw [hs, map_add, Prod.snd_add, hBT, zero_add] at h
  exact h

variable (e : OpenPartialHomeomorph (E × N) (E × N)) (a : E)
  (ha : (a, 0) ∈ e.source)
  (hplane : ∀ p ∈ e.source, (e p).2 = 0 ↔ p.2 = 0)
  (he : AnalyticAt ℂ e (a, 0)) (hei : AnalyticAt ℂ e.symm (e (a, 0)))

omit [NormedSpace ℂ E] [NormedSpace ℂ N] in
include ha hplane in
theorem normalTransition_center_normal : (e (a, 0)).2 = 0 :=
  (hplane (a, 0) ha).mpr rfl

include ha hplane he in
theorem normalTransition_tangent_derivative (v : E) :
    (fderiv ℂ e (a, 0) (v, 0)).2 = 0 := by
  apply normal_tangent_derivative_eq_zero he.differentiableAt.hasFDerivAt
  filter_upwards [(continuousAt_id.prodMk continuousAt_const)
    (e.open_source.mem_nhds ha)] with w hw
  exact (hplane (w, 0) hw).mpr rfl

include ha hplane hei in
theorem normalTransition_inverse_tangent_derivative (v : E) :
    (fderiv ℂ e.symm (e (a, 0)) (v, 0)).2 = 0 := by
  have hcenter : e (a, 0) = ((e (a, 0)).1, (0 : N)) :=
    Prod.ext rfl (normalTransition_center_normal e a ha hplane)
  have hder := hei.differentiableAt.hasFDerivAt
  rw [hcenter] at hder
  have htarget : ((e (a, 0)).1, (0 : N)) ∈ e.target := hcenter ▸ e.map_source ha
  have hzero : ∀ᶠ w in 𝓝 (e (a, 0)).1, (e.symm (w, 0)).2 = 0 := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const)
      (e.open_target.mem_nhds htarget)] with w hw
    change (w, 0) ∈ e.target at hw
    apply (hplane (e.symm (w, 0)) (e.map_target hw)).mp
    rw [e.right_inv hw]
  simpa only [← hcenter] using normal_tangent_derivative_eq_zero hder hzero v

include ha he hei in
theorem normalTransition_derivative_leftInverse :
    (fderiv ℂ e.symm (e (a, 0))).comp (fderiv ℂ e (a, 0)) =
      ContinuousLinearMap.id ℂ (E × N) := by
  have h := hei.differentiableAt.hasFDerivAt.comp (a, (0 : N)) he.differentiableAt.hasFDerivAt
  have hi : (e.symm ∘ e) =ᶠ[𝓝 (a, (0 : N))] id := e.eventually_left_inverse ha
  exact (h.congr_of_eventuallyEq hi.symm).unique (hasFDerivAt_id _)

include ha he hei in
theorem normalTransition_derivative_rightInverse :
    (fderiv ℂ e (a, 0)).comp (fderiv ℂ e.symm (e (a, 0))) =
      ContinuousLinearMap.id ℂ (E × N) := by
  have hder : HasFDerivAt e (fderiv ℂ e (a, 0)) (e.symm (e (a, 0))) := by
    rw [e.left_inv ha]
    exact he.differentiableAt.hasFDerivAt
  have h := hder.comp (e (a, 0)) hei.differentiableAt.hasFDerivAt
  have hi : (e ∘ e.symm) =ᶠ[𝓝 (e (a, (0 : N)))] id := e.eventually_right_inverse' ha
  exact (h.congr_of_eventuallyEq hi.symm).unique (hasFDerivAt_id _)

/-- The normal derivative is complex-linearly invertible, with inverse the actual normal
block of the derivative of the inverse chart. -/
def normalTransitionDerivativeEquiv : N ≃L[ℂ] N where
  toLinearEquiv :=
    { toLinearMap := normalBlock (fderiv ℂ e (a, 0))
      invFun := normalBlock (fderiv ℂ e.symm (e (a, 0)))
      left_inv := normalBlock_leftInverse _ _
        (normalTransition_derivative_leftInverse e a ha he hei)
        (normalTransition_inverse_tangent_derivative e a ha hplane hei)
      right_inv := normalBlock_leftInverse _ _
        (normalTransition_derivative_rightInverse e a ha he hei)
        (normalTransition_tangent_derivative e a ha hplane he) }
  continuous_toFun := (normalBlock (fderiv ℂ e (a, 0))).continuous
  continuous_invFun := (normalBlock (fderiv ℂ e.symm (e (a, 0)))).continuous

@[simp] theorem normalTransitionDerivativeEquiv_apply (v : N) :
    normalTransitionDerivativeEquiv e a ha hplane he hei v =
      (fderiv ℂ e (a, 0) (0, v)).2 := rfl

/-- The actual map on a transverse normal fiber has the constructed normal derivative. -/
theorem normalTransition_hasFDerivAt :
    HasFDerivAt (fun v : N => (e (a, v)).2)
      (normalTransitionDerivativeEquiv e a ha hplane he hei).toContinuousLinearMap 0 := by
  have h := (ContinuousLinearMap.snd ℂ E N).hasFDerivAt.comp (0 : N)
    (he.differentiableAt.hasFDerivAt.comp (0 : N) (hasFDerivAt_prodMk_right a 0))
  convert h using 1 <;> rfl

end GeneralNormal

section StandardNormal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (c : ℕ)
  (e : OpenPartialHomeomorph (E × (Fin c → ℂ)) (E × (Fin c → ℂ))) (a : E)
  (ha : (a, 0) ∈ e.source)
  (hplane : ∀ p ∈ e.source, (e p).2 = 0 ↔ p.2 = 0)
  (he : AnalyticAt ℂ e (a, 0)) (hei : AnalyticAt ℂ e.symm (e (a, 0)))

/-- The actual transverse normal map of a coordinate transition. -/
def normalTransitionMap (v : Fin c → ℂ) : Fin c → ℂ := (e (a, v)).2

/-- Only normal parameters whose full points are in the transition domain are used. -/
def normalTransitionDomain : Set (Fin c → ℂ) := {v | (a, v) ∈ e.source}

omit [NormedSpace ℂ E] in
theorem normalTransitionDomain_isOpen : IsOpen (normalTransitionDomain c e a) :=
  e.open_source.preimage (continuous_const.prodMk continuous_id)

omit [NormedSpace ℂ E] in
include ha hplane in
@[simp] theorem normalTransitionMap_zero : normalTransitionMap c e a 0 = 0 :=
  normalTransition_center_normal e a ha hplane

omit [NormedSpace ℂ E] in
theorem normalTransitionMap_continuousOn :
    ContinuousOn (normalTransitionMap c e a) (normalTransitionDomain c e a) :=
  (e.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hv => hv)).snd

include ha hplane he hei in
/-- The actual normal map preserves the exactly normalized complex class on a sufficiently
small normal neighborhood. The inverse normal derivative is proved above, not assumed. -/
theorem exists_open_normalTransition_localClass_invariance :
    ∃ (W : Set (Fin c → ℂ)) (hW : W ⊆ normalTransitionDomain c e a)
      (hne : ∀ v, v ∈ W → v ≠ 0 → normalTransitionMap c e a v ≠ 0),
      IsOpen W ∧ 0 ∈ W ∧
      ∀ z : RelativeHomology ℚ (neighborhoodPointComplementPair W 0) (2 * c),
        relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap W 0) z =
          standardComplexLocalClass c →
        relativeHomologyMap ℚ (2 * c)
          (complexNeighborhoodPuncturedPairMapOf c W (normalTransitionMap c e a)
            ((normalTransitionMap_continuousOn c e a).mono hW)
            (normalTransitionMap_zero c e a ha hplane) hne) z = standardComplexLocalClass c := by
  let L := normalTransitionDerivativeEquiv e a ha hplane he hei
  let A := complexMatrixOfContinuousLinearMap c L.toContinuousLinearMap
  have hA : A.det ≠ 0 :=
    complexMatrixOfContinuousLinearMap_det_ne_zero c L.toContinuousLinearMap L.injective
  have hAL : (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) =
      L.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun v =>
      complexMatrixOfContinuousLinearMap_mulVec c L.toContinuousLinearMap v
  apply exists_open_complexDifferentiable_localClass_invariance c A hA
    (normalTransitionDomain c e a) (normalTransitionDomain_isOpen c e a) ha
    (normalTransitionMap c e a) (normalTransitionMap_continuousOn c e a)
    (normalTransitionMap_zero c e a ha hplane)
  rw [hAL]
  exact normalTransition_hasFDerivAt e a ha hplane he hei

include ha hplane he hei in
/-- On a smaller actual normal neighborhood, the normal transition and inclusion induce
the same top relative-homology map. This strengthens preservation of one normalized class
to the equality needed to compare coclass pullbacks. -/
theorem exists_open_normalTransition_relativeHomologyMap_eq :
    ∃ (W : Set (Fin c → ℂ)) (hW : W ⊆ normalTransitionDomain c e a)
      (hne : ∀ v, v ∈ W → v ≠ 0 → normalTransitionMap c e a v ≠ 0),
      IsOpen W ∧ 0 ∈ W ∧
      relativeHomologyMap ℚ (2 * c)
        (complexNeighborhoodPuncturedPairMapOf c W (normalTransitionMap c e a)
          ((normalTransitionMap_continuousOn c e a).mono hW)
          (normalTransitionMap_zero c e a ha hplane) hne) =
        relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap W 0) := by
  obtain ⟨W, hW, hne, hWo, h0W, hclass⟩ :=
    exists_open_normalTransition_localClass_invariance c e a ha hplane he hei
  refine ⟨W, hW, hne, hWo, h0W, ?_⟩
  have hb := neighborhoodPointComplement_relativeHomologyMap_bijective W 0 hWo h0W (2 * c)
  obtain ⟨z₀, hz₀⟩ := hb.2 (standardComplexLocalClass c)
  have hzmap := hclass z₀ hz₀
  ext z
  obtain ⟨r, hr⟩ := (Submodule.span_singleton_eq_top_iff ℚ (standardComplexLocalClass c)).mp
    (span_standardComplexLocalClass_eq_top_for_chart c)
    (relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap W 0) z)
  have hz : r • z₀ = z := hb.1 (by rw [map_smul, hz₀]; exact hr)
  rw [← hz, map_smul, map_smul, hzmap, hz₀]

include ha hplane he hei in
/-- Therefore the actual normal transition and inclusion have identical top relative
cohomology pullbacks, in particular for the fixed normalized normal coclass. -/
theorem exists_open_normalTransition_relativeCohomologyMap_eq :
    ∃ (W : Set (Fin c → ℂ)) (hW : W ⊆ normalTransitionDomain c e a)
      (hne : ∀ v, v ∈ W → v ≠ 0 → normalTransitionMap c e a v ≠ 0),
      IsOpen W ∧ 0 ∈ W ∧
      relativeCohomologyMap ℚ (2 * c)
        (complexNeighborhoodPuncturedPairMapOf c W (normalTransitionMap c e a)
          ((normalTransitionMap_continuousOn c e a).mono hW)
          (normalTransitionMap_zero c e a ha hplane) hne) =
        relativeCohomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap W 0) := by
  obtain ⟨W, hW, hne, hWo, h0W, heq⟩ :=
    exists_open_normalTransition_relativeHomologyMap_eq c e a ha hplane he hei
  exact ⟨W, hW, hne, hWo, h0W, congrArg LinearMap.dualMap heq⟩

end StandardNormal

end AlgebraicTopology.Singular
