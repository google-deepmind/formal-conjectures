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

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The radial homotopy operator on differential forms

This file develops the radial homotopy operator used in the Poincaré lemma.  For a differential
`(n + 1)`-form `ω` on a complex normed vector space, its radial contraction is

`Hω(x) = ∫ t in 0..1, t ^ n • ω(t • x)(x, ·) dt`.

The construction is explicit.  In particular, exactness will not be introduced as an assumption.
-/

@[expose] public noncomputable section

open ContinuousAlternatingMap MeasureTheory
open scoped ContDiff Interval

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]

omit [Nontrivial E] in
/-- A point of a real radial segment stays in a star-convex set. -/
lemma smul_mem_of_starConvex_zero {s : Set E} (hstar : StarConvex ℝ 0 s)
    {x : E} (hx : x ∈ s) {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (t : ℂ) • x ∈ s := by
  have hmem := hstar.segment_subset hx (lineMap_mem_segment ℝ (0 : E) x ht)
  simpa [AffineMap.lineMap_apply] using hmem

section ParametricIntegral

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [CompleteSpace G] [FiniteDimensional ℂ E]

omit [Nontrivial E] [CompleteSpace G] in
/-- A continuously varying family of complex Fréchet derivatives can be integrated over a
compact real interval.  This is the compact-parameter specialization of differentiation under the
integral sign needed below. -/
theorem hasFDerivAt_intervalIntegral_of_continuous
    (F : E → ℝ → G) (F' : E → ℝ → E →L[ℂ] G) (x₀ : E)
    (hF : Continuous fun p : E × ℝ ↦ F p.1 p.2)
    (hF' : Continuous fun p : E × ℝ ↦ F' p.1 p.2)
    (hdiff : ∀ x t, HasFDerivAt (F · t) (F' x t) x) :
    HasFDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, F x t)
      (∫ t in (0 : ℝ)..1, F' x₀ t) x₀ := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  let K : Set (E × ℝ) := Metric.closedBall x₀ 1 ×ˢ Set.Icc 0 1
  have hK : IsCompact K := (isCompact_closedBall x₀ 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Metric.ball x₀ 1) (bound := fun _ ↦ C)
  · exact Metric.ball_mem_nhds x₀ one_pos
  · filter_upwards [] with x
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.intervalIntegrable
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hC (x, t) ⟨Metric.ball_subset_closedBall hx, ht.1.le, ht.2⟩
  · exact continuousOn_const.intervalIntegrable
  · filter_upwards [] with t ht x hx
    exact hdiff x t

omit [Nontrivial E] [CompleteSpace G] in
/-- A local version of differentiation under a compact parameter integral.  The functions and
their space derivatives need only be continuous on an open neighborhood, uniformly for parameters
in `[0, 1]`. -/
theorem hasFDerivAt_intervalIntegral_of_continuousOn
    (F : E → ℝ → G) (F' : E → ℝ → E →L[ℂ] G) {s : Set E} (x₀ : E)
    (hs : IsOpen s) (hx₀ : x₀ ∈ s)
    (hF : ContinuousOn (fun p : E × ℝ ↦ F p.1 p.2) (s ×ˢ Set.Icc 0 1))
    (hF' : ContinuousOn (fun p : E × ℝ ↦ F' p.1 p.2) (s ×ˢ Set.Icc 0 1))
    (hdiff : ∀ x ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt (F · t) (F' x t) x) :
    HasFDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, F x t)
      (∫ t in (0 : ℝ)..1, F' x₀ t) x₀ := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx₀)
  let K : Set (E × ℝ) := Metric.closedBall x₀ ε ×ˢ Set.Icc 0 1
  have hK : IsCompact K := (isCompact_closedBall x₀ ε).prod isCompact_Icc
  have hF'K : ContinuousOn (fun p : E × ℝ ↦ F' p.1 p.2) K :=
    hF'.mono (Set.prod_mono hεs subset_rfl)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'K
  have hFslice (x : E) (hx : x ∈ s) : ContinuousOn (F x) (Set.Icc 0 1) := by
    change ContinuousOn (fun t ↦ F x t) (Set.Icc 0 1)
    simpa only [Function.comp_def, id_eq] using hF.comp
      (continuousOn_const.prodMk continuousOn_id) (fun t ht ↦ ⟨hx, ht⟩)
  have hF'slice (x : E) (hx : x ∈ s) : ContinuousOn (F' x) (Set.Icc 0 1) := by
    change ContinuousOn (fun t ↦ F' x t) (Set.Icc 0 1)
    simpa only [Function.comp_def, id_eq] using hF'.comp
      (continuousOn_const.prodMk continuousOn_id) (fun t ht ↦ ⟨hx, ht⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Metric.ball x₀ ε) (bound := fun _ ↦ C)
  · exact Metric.ball_mem_nhds x₀ hε
  · filter_upwards [hs.mem_nhds hx₀] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hFslice x hx).mono Set.Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  · exact (hFslice x₀ hx₀).intervalIntegrable_of_Icc (by norm_num)
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hF'slice x₀ hx₀).mono Set.Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [] with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hC (x, t) ⟨Metric.ball_subset_closedBall hx, ht.1.le, ht.2⟩
  · exact continuousOn_const.intervalIntegrable
  · filter_upwards [] with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hdiff x (hεs (Metric.ball_subset_closedBall hx)) t ⟨ht.1.le, ht.2⟩

omit [Nontrivial E] [NormedSpace ℂ G] [CompleteSpace G] in
/-- A compact parameter integral is continuous on an open parameter domain when its integrand is
jointly continuous there. -/
theorem continuousOn_intervalIntegral_of_continuousOn
    (F : E → ℝ → G) {s : Set E} (hs : IsOpen s)
    (hF : ContinuousOn (fun p : E × ℝ ↦ F p.1 p.2) (s ×ˢ Set.Icc 0 1)) :
    ContinuousOn (fun x ↦ ∫ t in (0 : ℝ)..1, F x t) s := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  intro x₀ hx₀
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx₀)
  let K : Set (E × ℝ) := Metric.closedBall x₀ ε ×ˢ Set.Icc 0 1
  have hK : IsCompact K := (isCompact_closedBall x₀ ε).prod isCompact_Icc
  have hFK : ContinuousOn (fun p : E × ℝ ↦ F p.1 p.2) K :=
    hF.mono (Set.prod_mono hεs subset_rfl)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hFK
  have hFtime (x : E) (hx : x ∈ s) : ContinuousOn (F x) (Set.Icc 0 1) := by
    change ContinuousOn (fun t ↦ F x t) (Set.Icc 0 1)
    simpa only [Function.comp_def, id_eq] using hF.comp
      (continuousOn_const.prodMk continuousOn_id) (fun t ht ↦ ⟨hx, ht⟩)
  have hFspace (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ContinuousOn (fun x ↦ F x t) s := by
    simpa only [Function.comp_def, id_eq] using hF.comp
      (continuousOn_id.prodMk continuousOn_const) (fun x hx ↦ ⟨hx, ht⟩)
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ ↦ C)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hFtime x hx).mono Set.Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x₀ hε)] with x hx hxb
    filter_upwards [] with t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hC (x, t) ⟨Metric.ball_subset_closedBall hxb, ht.1.le, ht.2⟩
  · exact continuousOn_const.intervalIntegrable
  · filter_upwards [] with t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hFspace t ⟨ht.1.le, ht.2⟩ x₀ hx₀

end ParametricIntegral

omit [Nontrivial E] in
/-- Joint evaluation of the first curried variable is a bounded bilinear map. -/
lemma isBoundedBilinearMap_curryLeft (n : ℕ) : IsBoundedBilinearMap ℂ
    (fun p : (E [⋀^Fin (n + 1)]→L[ℂ] ℂ) × E ↦ p.1.curryLeft p.2) where
  add_left f g x := by simp
  smul_left c f x := by simp
  add_right f x y := by simp
  smul_right c f x := by simp
  bound := ⟨1, one_pos, fun f x ↦ by
    simpa only [one_mul, ContinuousAlternatingMap.norm_curryLeft] using
      (f.curryLeft.le_opNorm x)⟩

/-- The integrand in the radial homotopy operator on an `(n + 1)`-form. -/
def radialIntegrand (n : ℕ) (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (t : ℝ) (x : E) : E [⋀^Fin n]→L[ℂ] ℂ :=
  ((t : ℂ) ^ n) • (η ((t : ℂ) • x)).curryLeft x

/-- The radial homotopy operator, obtained by integrating contraction with the radial vector
field along scalar dilations. -/
def radialHomotopy (n : ℕ) (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (x : E) : E [⋀^Fin n]→L[ℂ] ℂ :=
  ∫ t : ℝ in 0..1, radialIntegrand n η t x

/-- The Fréchet derivative of the radial integrand with respect to its space variable. -/
def radialIntegrandFDeriv (n : ℕ) (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (t : ℝ) (x : E) : E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ :=
  ((t : ℂ) ^ n) •
    ((isBoundedBilinearMap_curryLeft (E := E) n).deriv (η ((t : ℂ) • x), x)).comp
      (((fderiv ℂ η ((t : ℂ) • x)).comp
        ((t : ℂ) • ContinuousLinearMap.id ℂ E)).prod (ContinuousLinearMap.id ℂ E))

omit [Nontrivial E] in
@[simp] lemma radialIntegrand_apply (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (t : ℝ) (x : E) (v : Fin n → E) :
    radialIntegrand n η t x v =
      ((t : ℂ) ^ n) • η ((t : ℂ) • x) (Matrix.vecCons x v) := rfl

omit [Nontrivial E] in
lemma radialIntegrand_differentiableAt (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : Differentiable ℂ η)
    (t : ℝ) (x : E) : DifferentiableAt ℂ (radialIntegrand n η t) x := by
  change DifferentiableAt ℂ
    (fun y ↦ ((t : ℂ) ^ n) • (η ((t : ℂ) • y)).curryLeft y) x
  have hscale : DifferentiableAt ℂ (fun y : E ↦ (t : ℂ) • y) x :=
    ((t : ℂ) • ContinuousLinearMap.id ℂ E).differentiableAt
  have hcomp : DifferentiableAt ℂ (fun y : E ↦ η ((t : ℂ) • y)) x :=
    (hη _).comp x hscale
  have hp := hcomp.prodMk differentiableAt_id
  exact (((isBoundedBilinearMap_curryLeft (E := E) n).differentiableAt _).comp x hp).const_smul
    ((t : ℂ) ^ n)

omit [Nontrivial E] in
lemma radialIntegrand_contDiff (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ ω η)
    (t : ℝ) : ContDiff ℂ ω (radialIntegrand n η t) := by
  change ContDiff ℂ ω
    (fun x ↦ ((t : ℂ) ^ n) • (η ((t : ℂ) • x)).curryLeft x)
  have hscale : ContDiff ℂ ω (fun x : E ↦ (t : ℂ) • x) :=
    ((t : ℂ) • ContinuousLinearMap.id ℂ E).contDiff
  have hcomp : ContDiff ℂ ω (fun x : E ↦ η ((t : ℂ) • x)) := hη.comp hscale
  exact (isBoundedBilinearMap_curryLeft (E := E) n).contDiff.comp
    (hcomp.prodMk contDiff_id) |>.const_smul ((t : ℂ) ^ n)

omit [Nontrivial E] in
lemma radialIntegrand_hasFDerivAt (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (t : ℝ) (x : E) (hη : DifferentiableAt ℂ η ((t : ℂ) • x)) :
    HasFDerivAt (radialIntegrand n η t) (radialIntegrandFDeriv n η t x) x := by
  have hscale : HasFDerivAt (fun y : E ↦ (t : ℂ) • y)
      ((t : ℂ) • ContinuousLinearMap.id ℂ E) x :=
    ((t : ℂ) • ContinuousLinearMap.id ℂ E).hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E ↦ η ((t : ℂ) • y))
      ((fderiv ℂ η ((t : ℂ) • x)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)) x :=
    hη.hasFDerivAt.comp x hscale
  have hpair := hcomp.prodMk (ContinuousLinearMap.id ℂ E).hasFDerivAt
  exact (((isBoundedBilinearMap_curryLeft (E := E) n).hasFDerivAt _).comp x hpair).const_smul
    ((t : ℂ) ^ n)

omit [Nontrivial E] in
lemma continuous_radialIntegrand (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : Continuous η) :
    Continuous fun p : E × ℝ ↦ radialIntegrand n η p.2 p.1 := by
  have hs : Continuous fun p : E × ℝ ↦ (p.2 : ℂ) • p.1 :=
    (Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst
  exact (Complex.continuous_ofReal.comp continuous_snd).pow n |>.smul <|
    (isBoundedBilinearMap_curryLeft (E := E) n).continuous.comp
      ((hη.comp hs).prodMk continuous_fst)

omit [Nontrivial E] in
lemma continuous_radialIntegrandFDeriv (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η) :
    Continuous fun p : E × ℝ ↦ radialIntegrandFDeriv n η p.2 p.1 := by
  have hs : Continuous fun p : E × ℝ ↦ (p.2 : ℂ) • p.1 :=
    (Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst
  have hDη : Continuous fun p : E × ℝ ↦ fderiv ℂ η ((p.2 : ℂ) • p.1) :=
    (hη.continuous_fderiv one_ne_zero).comp hs
  have hscale : Continuous fun p : E × ℝ ↦
      (p.2 : ℂ) • ContinuousLinearMap.id ℂ E :=
    (Complex.continuous_ofReal.comp continuous_snd).smul continuous_const
  have hinner : Continuous fun p : E × ℝ ↦
      ((fderiv ℂ η ((p.2 : ℂ) • p.1)).comp
        ((p.2 : ℂ) • ContinuousLinearMap.id ℂ E)).prod (ContinuousLinearMap.id ℂ E) :=
    (ContinuousLinearMap.prodL ℂ).continuous.comp
      ((hDη.clm_comp hscale).prodMk continuous_const)
  have houter : Continuous fun p : E × ℝ ↦
      (isBoundedBilinearMap_curryLeft (E := E) n).deriv
        (η ((p.2 : ℂ) • p.1), p.1) :=
    (isBoundedBilinearMap_curryLeft (E := E) n).isBoundedLinearMap_deriv.continuous.comp
      ((hη.continuous.comp hs).prodMk continuous_fst)
  exact (Complex.continuous_ofReal.comp continuous_snd).pow n |>.smul
    (houter.clm_comp hinner)

omit [Nontrivial E] in
lemma continuousOn_radialIntegrand (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hstar : StarConvex ℝ 0 s)
    (hη : ContinuousOn η s) :
    ContinuousOn (fun p : E × ℝ ↦ radialIntegrand n η p.2 p.1)
      (s ×ˢ Set.Icc 0 1) := by
  have hs : ContinuousOn (fun p : E × ℝ ↦ (p.2 : ℂ) • p.1)
      (s ×ˢ Set.Icc 0 1) :=
    ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst).continuousOn
  have hsmap : Set.MapsTo (fun p : E × ℝ ↦ (p.2 : ℂ) • p.1)
      (s ×ˢ Set.Icc 0 1) s := fun p hp ↦ smul_mem_of_starConvex_zero hstar hp.1 hp.2
  have hηscale : ContinuousOn (fun p : E × ℝ ↦ η ((p.2 : ℂ) • p.1))
      (s ×ˢ Set.Icc 0 1) := by
    simpa only [Function.comp_def] using hη.comp hs hsmap
  have hpair : ContinuousOn (fun p : E × ℝ ↦ (η ((p.2 : ℂ) • p.1), p.1))
      (s ×ˢ Set.Icc 0 1) := hηscale.prodMk continuousOn_fst
  have hcurry : ContinuousOn (fun p : E × ℝ ↦ (η ((p.2 : ℂ) • p.1)).curryLeft p.1)
      (s ×ˢ Set.Icc 0 1) := by
    simpa only [Function.comp_def] using
      (isBoundedBilinearMap_curryLeft (E := E) n).continuous.comp_continuousOn hpair
  have hpow : ContinuousOn (fun p : E × ℝ ↦ (p.2 : ℂ) ^ n)
      (s ×ˢ Set.Icc 0 1) :=
    (Complex.continuous_ofReal.comp continuous_snd).pow n |>.continuousOn
  exact hpow.smul hcurry

omit [Nontrivial E] in
lemma continuousOn_radialIntegrandFDeriv (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s) :
    ContinuousOn (fun p : E × ℝ ↦ radialIntegrandFDeriv n η p.2 p.1)
      (s ×ˢ Set.Icc 0 1) := by
  have hscalePoint : ContinuousOn (fun p : E × ℝ ↦ (p.2 : ℂ) • p.1)
      (s ×ˢ Set.Icc 0 1) :=
    ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst).continuousOn
  have hsmap : Set.MapsTo (fun p : E × ℝ ↦ (p.2 : ℂ) • p.1)
      (s ×ˢ Set.Icc 0 1) s := fun p hp ↦ smul_mem_of_starConvex_zero hstar hp.1 hp.2
  have hDη : ContinuousOn (fun p : E × ℝ ↦ fderiv ℂ η ((p.2 : ℂ) • p.1))
      (s ×ˢ Set.Icc 0 1) :=
    (hη.continuousOn_fderiv_of_isOpen hs le_rfl).comp hscalePoint hsmap
  have hscale : ContinuousOn (fun p : E × ℝ ↦
      (p.2 : ℂ) • ContinuousLinearMap.id ℂ E) (s ×ˢ Set.Icc 0 1) :=
    ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const).continuousOn
  have hcomp : ContinuousOn (fun p : E × ℝ ↦
      (fderiv ℂ η ((p.2 : ℂ) • p.1)).comp
        ((p.2 : ℂ) • ContinuousLinearMap.id ℂ E)) (s ×ˢ Set.Icc 0 1) :=
    hDη.clm_comp hscale
  have hpairInner : ContinuousOn (fun p : E × ℝ ↦
      ((fderiv ℂ η ((p.2 : ℂ) • p.1)).comp
        ((p.2 : ℂ) • ContinuousLinearMap.id ℂ E), ContinuousLinearMap.id ℂ E))
      (s ×ˢ Set.Icc 0 1) := hcomp.prodMk continuousOn_const
  have hinner : ContinuousOn (fun p : E × ℝ ↦
      ((fderiv ℂ η ((p.2 : ℂ) • p.1)).comp
        ((p.2 : ℂ) • ContinuousLinearMap.id ℂ E)).prod (ContinuousLinearMap.id ℂ E))
      (s ×ˢ Set.Icc 0 1) := by
    simpa only [Function.comp_def] using!
      (ContinuousLinearMap.prodL ℂ).continuous.comp_continuousOn hpairInner
  have hηscale : ContinuousOn (fun p : E × ℝ ↦ η ((p.2 : ℂ) • p.1))
      (s ×ˢ Set.Icc 0 1) := by
    simpa only [Function.comp_def] using hη.continuousOn.comp hscalePoint hsmap
  have hpairOuter : ContinuousOn (fun p : E × ℝ ↦ (η ((p.2 : ℂ) • p.1), p.1))
      (s ×ˢ Set.Icc 0 1) := hηscale.prodMk continuousOn_fst
  have houter : ContinuousOn (fun p : E × ℝ ↦
      (isBoundedBilinearMap_curryLeft (E := E) n).deriv
        (η ((p.2 : ℂ) • p.1), p.1)) (s ×ˢ Set.Icc 0 1) :=
    by simpa only [Function.comp_def] using
      (isBoundedBilinearMap_curryLeft (E := E) n).isBoundedLinearMap_deriv.continuous.comp_continuousOn
        hpairOuter
  have hpow : ContinuousOn (fun p : E × ℝ ↦ (p.2 : ℂ) ^ n)
      (s ×ˢ Set.Icc 0 1) :=
    (Complex.continuous_ofReal.comp continuous_snd).pow n |>.continuousOn
  exact hpow.smul (houter.clm_comp hinner)

omit [Nontrivial E] in
lemma radialHomotopy_hasFDerivAt [FiniteDimensional ℂ E] (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η) (x : E) :
    HasFDerivAt (radialHomotopy n η)
      (∫ t : ℝ in 0..1, radialIntegrandFDeriv n η t x) x :=
  hasFDerivAt_intervalIntegral_of_continuous
    (fun x t ↦ radialIntegrand n η t x) (fun x t ↦ radialIntegrandFDeriv n η t x) x
    (continuous_radialIntegrand n η hη.continuous)
    (continuous_radialIntegrandFDeriv n η hη)
    (fun x t ↦ radialIntegrand_hasFDerivAt n η t x
      (hη.differentiable one_ne_zero ((t : ℂ) • x)))

omit [Nontrivial E] in
/-- The radial homotopy is differentiable at an interior point using only first-order smoothness on
an open star-convex domain. -/
lemma radialHomotopy_hasFDerivAt_of_contDiffOn [FiniteDimensional ℂ E] (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s) {x : E} (hx : x ∈ s) :
    HasFDerivAt (radialHomotopy n η)
      (∫ t : ℝ in 0..1, radialIntegrandFDeriv n η t x) x :=
  hasFDerivAt_intervalIntegral_of_continuousOn
    (fun y t ↦ radialIntegrand n η t y) (fun y t ↦ radialIntegrandFDeriv n η t y)
    x hs hx (continuousOn_radialIntegrand n η hstar hη.continuousOn)
    (continuousOn_radialIntegrandFDeriv n η hs hstar hη)
    (fun y hy t ht ↦ radialIntegrand_hasFDerivAt n η t y <|
      (hη.contDiffAt (hs.mem_nhds (smul_mem_of_starConvex_zero hstar hy ht))).differentiableAt
        one_ne_zero)

omit [Nontrivial E] in
/-- First-order regularity of the radial homotopy on an open star-convex domain. -/
theorem radialHomotopy_contDiffOn_one [FiniteDimensional ℂ E] (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s) :
    ContDiffOn ℂ 1 (radialHomotopy n η) s := by
  let : NormedAddCommGroup (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by
    with_reducible_and_instances exact ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℂ (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by
    with_reducible_and_instances exact ContinuousLinearMap.toNormedSpace
  let : NormedSpace ℝ (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let : CompleteSpace (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by infer_instance
  have hD : ContinuousOn
      (fun x ↦ ∫ t : ℝ in 0..1, radialIntegrandFDeriv n η t x) s :=
    continuousOn_intervalIntegral_of_continuousOn
      (fun x t ↦ radialIntegrandFDeriv n η t x) hs
      (continuousOn_radialIntegrandFDeriv n η hs hstar hη)
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl, contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨?_, by simp, ?_⟩
  · exact fun x hx ↦ (radialHomotopy_hasFDerivAt_of_contDiffOn n η hs hstar hη hx).differentiableAt
      |>.differentiableWithinAt
  · rw [contDiffOn_zero]
    exact hD.congr fun x hx ↦ (radialHomotopy_hasFDerivAt_of_contDiffOn n η hs hstar hη hx).fderiv

omit [Nontrivial E] in
/-- Exterior differentiation commutes with the radial parameter integral. -/
theorem extDeriv_radialHomotopy [FiniteDimensional ℂ E] (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η) (x : E) :
    extDeriv (radialHomotopy n η) x =
      ∫ t : ℝ in 0..1, extDeriv (radialIntegrand n η t) x := by
  let : NormedAddCommGroup (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by
    with_reducible_and_instances exact ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℂ (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by
    with_reducible_and_instances exact ContinuousLinearMap.toNormedSpace
  let : NormedSpace ℝ (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let : CompleteSpace (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by infer_instance
  have hF' : Continuous fun t : ℝ ↦ radialIntegrandFDeriv n η t x :=
    (continuous_radialIntegrandFDeriv n η hη).comp (continuous_const.prodMk continuous_id)
  with_reducible_and_instances
    have hF'int : IntervalIntegrable (fun t : ℝ ↦ radialIntegrandFDeriv n η t x)
        MeasureTheory.volume 0 1 := hF'.continuousOn.intervalIntegrable
    rw [extDeriv, (radialHomotopy_hasFDerivAt n η hη x).fderiv]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    rw [← (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ E ℂ).intervalIntegral_comp_comm
      hF'int]
  apply intervalIntegral.integral_congr
  intro t _
  change ContinuousAlternatingMap.alternatizeUncurryFin (radialIntegrandFDeriv n η t x) =
    ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℂ (radialIntegrand n η t) x)
  rw [(radialIntegrand_hasFDerivAt n η t x
    (hη.differentiable one_ne_zero ((t : ℂ) • x))).fderiv]

omit [Nontrivial E] in
/-- Exterior differentiation commutes with the radial integral at points of an open star-convex
domain.  Only the restriction of the form to the domain is assumed continuously differentiable. -/
theorem extDeriv_radialHomotopy_of_contDiffOn [FiniteDimensional ℂ E] (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s) {x : E} (hx : x ∈ s) :
    extDeriv (radialHomotopy n η) x =
      ∫ t : ℝ in 0..1, extDeriv (radialIntegrand n η t) x := by
  let : NormedAddCommGroup (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by
    with_reducible_and_instances exact ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℂ (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by
    with_reducible_and_instances exact ContinuousLinearMap.toNormedSpace
  let : NormedSpace ℝ (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let : CompleteSpace (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) := by infer_instance
  have hF' : ContinuousOn (fun t : ℝ ↦ radialIntegrandFDeriv n η t x) (Set.Icc 0 1) := by
    have h := (continuousOn_radialIntegrandFDeriv n η hs hstar hη).comp
      (continuousOn_const.prodMk continuousOn_id) (fun t ht ↦ ⟨hx, ht⟩)
    simpa only [Function.comp_def, id_eq] using h
  with_reducible_and_instances
    have hF'int : IntervalIntegrable (fun t : ℝ ↦ radialIntegrandFDeriv n η t x)
        MeasureTheory.volume 0 1 := hF'.intervalIntegrable_of_Icc (by norm_num)
    rw [extDeriv, (radialHomotopy_hasFDerivAt_of_contDiffOn n η hs hstar hη hx).fderiv]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    rw [← (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ E ℂ).intervalIntegral_comp_comm
      hF'int]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  change ContinuousAlternatingMap.alternatizeUncurryFin (radialIntegrandFDeriv n η t x) =
    ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℂ (radialIntegrand n η t) x)
  rw [(radialIntegrand_hasFDerivAt n η t x <|
    (hη.contDiffAt (hs.mem_nhds (smul_mem_of_starConvex_zero hstar hx ht'))).differentiableAt
      one_ne_zero).fderiv]

/-- The part of the derivative of a contraction that differentiates the alternating form. -/
def curryDerivativeAt (n : ℕ) (L : E →L[ℂ] E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (x : E) :
    E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ :=
  ((isBoundedBilinearMap_curryLeft (E := E) n).deriv (0, x)).comp
    (L.prod (0 : E →L[ℂ] E))

omit [Nontrivial E] in
@[simp] lemma curryDerivativeAt_apply (n : ℕ)
    (L : E →L[ℂ] E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (x h : E) :
    curryDerivativeAt n L x h = (L h).curryLeft x := by
  simp [curryDerivativeAt, IsBoundedBilinearMap.deriv_apply]

omit [Nontrivial E] in
/-- The algebraic cancellation at the heart of Cartan's radial homotopy formula. -/
theorem alternatize_curryDerivativeAt_add (n : ℕ)
    (L : E →L[ℂ] E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (x : E) :
    ContinuousAlternatingMap.alternatizeUncurryFin (curryDerivativeAt n L x) +
      (ContinuousAlternatingMap.alternatizeUncurryFin L).curryLeft x = L x := by
  ext v
  have hremove (i : Fin (n + 1)) :
      i.succ.removeNth (Matrix.vecCons x v) = Matrix.vecCons x (i.removeNth v) := by
    change (Fin.cons x v) ∘ i.succ.succAbove = Fin.cons x (i.removeNth v)
    exact Fin.cons_comp_succ_succAbove x v i
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ, pow_succ,
    hremove]
  abel

omit [Nontrivial E] in
lemma radialIntegrandFDeriv_eq (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (t : ℝ) (x : E) :
    radialIntegrandFDeriv n η t x =
      ((t : ℂ) ^ n) • ((η ((t : ℂ) • x)).curryLeft +
        (t : ℂ) • curryDerivativeAt n (fderiv ℂ η ((t : ℂ) • x)) x) := by
  ext h v
  simp [radialIntegrandFDeriv, curryDerivativeAt, IsBoundedBilinearMap.deriv_apply,
    smul_add, smul_smul]
  ring

omit [Nontrivial E] in
/-- Exterior derivative of the radial integrand, before adding the contraction of `dη`. -/
theorem extDeriv_radialIntegrand (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (t : ℝ) (x : E)
    (hη : DifferentiableAt ℂ η ((t : ℂ) • x)) :
    extDeriv (radialIntegrand n η t) x =
      (((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n) • η ((t : ℂ) • x) +
        (t : ℂ) ^ (n + 1) • ContinuousAlternatingMap.alternatizeUncurryFin
          (curryDerivativeAt n (fderiv ℂ η ((t : ℂ) • x)) x) := by
  rw [extDeriv, (radialIntegrand_hasFDerivAt n η t x hη).fderiv,
    radialIntegrandFDeriv_eq]
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_smul,
    ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft, Nat.cast_add, Nat.cast_one,
    smul_add, smul_smul, pow_succ']
  module

omit [Nontrivial E] in
/-- Pointwise Cartan formula for dilation along the radial vector field. -/
theorem extDeriv_radialIntegrand_add (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (t : ℝ) (x : E)
    (hη : DifferentiableAt ℂ η ((t : ℂ) • x)) :
    extDeriv (radialIntegrand n η t) x + radialIntegrand (n + 1) (extDeriv η) t x =
      (((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n) • η ((t : ℂ) • x) +
        (t : ℂ) ^ (n + 1) • fderiv ℂ η ((t : ℂ) • x) x := by
  rw [extDeriv_radialIntegrand n η t x hη]
  change _ + ((t : ℂ) ^ (n + 1)) •
      (ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℂ η ((t : ℂ) • x))).curryLeft x = _
  rw [add_assoc, ← smul_add, alternatize_curryDerivativeAt_add]

/-- The pullback of an `(n + 1)`-form by scalar dilation. -/
def radialPullback (n : ℕ) (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (x : E) (t : ℝ) : E [⋀^Fin (n + 1)]→L[ℂ] ℂ :=
  ((t : ℂ) ^ (n + 1)) • η ((t : ℂ) • x)

/-- The derivative of `radialPullback` in its real dilation parameter. -/
def radialPullbackDeriv (n : ℕ) (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (x : E) (t : ℝ) : E [⋀^Fin (n + 1)]→L[ℂ] ℂ :=
  (((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n) • η ((t : ℂ) • x) +
    (t : ℂ) ^ (n + 1) • fderiv ℂ η ((t : ℂ) • x) x

omit [Nontrivial E] in
lemma continuous_radialPullback (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : Continuous η) (x : E) :
    Continuous (radialPullback n η x) :=
  (Complex.continuous_ofReal.pow (n + 1)).smul <|
    hη.comp (Complex.continuous_ofReal.smul continuous_const)

omit [Nontrivial E] in
lemma continuous_radialPullbackDeriv (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η) (x : E) :
    Continuous (radialPullbackDeriv n η x) := by
  have hline : Continuous fun t : ℝ ↦ (t : ℂ) • x :=
    Complex.continuous_ofReal.smul continuous_const
  have hDf : Continuous fun t : ℝ ↦ fderiv ℂ η ((t : ℂ) • x) x :=
    ((hη.continuous_fderiv one_ne_zero).comp hline).clm_apply continuous_const
  exact (((continuous_const.mul (Complex.continuous_ofReal.pow n)).smul
    (hη.continuous.comp hline)).add <|
      (Complex.continuous_ofReal.pow (n + 1)).smul hDf)

omit [Nontrivial E] in
lemma continuousOn_radialPullback (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hstar : StarConvex ℝ 0 s)
    (hη : ContinuousOn η s) {x : E} (hx : x ∈ s) :
    ContinuousOn (radialPullback n η x) (Set.Icc 0 1) := by
  have hline : ContinuousOn (fun t : ℝ ↦ (t : ℂ) • x) (Set.Icc 0 1) :=
    (Complex.continuous_ofReal.smul continuous_const).continuousOn
  have hmap : Set.MapsTo (fun t : ℝ ↦ (t : ℂ) • x) (Set.Icc 0 1) s :=
    fun t ht ↦ smul_mem_of_starConvex_zero hstar hx ht
  have hform : ContinuousOn (fun t : ℝ ↦ η ((t : ℂ) • x)) (Set.Icc 0 1) := by
    simpa only [Function.comp_def] using hη.comp hline hmap
  exact (Complex.continuous_ofReal.pow (n + 1)).continuousOn.smul hform

omit [Nontrivial E] in
lemma continuousOn_radialPullbackDeriv (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s) {x : E} (hx : x ∈ s) :
    ContinuousOn (radialPullbackDeriv n η x) (Set.Icc 0 1) := by
  have hline : ContinuousOn (fun t : ℝ ↦ (t : ℂ) • x) (Set.Icc 0 1) :=
    (Complex.continuous_ofReal.smul continuous_const).continuousOn
  have hmap : Set.MapsTo (fun t : ℝ ↦ (t : ℂ) • x) (Set.Icc 0 1) s :=
    fun t ht ↦ smul_mem_of_starConvex_zero hstar hx ht
  have hform : ContinuousOn (fun t : ℝ ↦ η ((t : ℂ) • x)) (Set.Icc 0 1) := by
    simpa only [Function.comp_def] using hη.continuousOn.comp hline hmap
  have hDf : ContinuousOn (fun t : ℝ ↦ fderiv ℂ η ((t : ℂ) • x) x)
      (Set.Icc 0 1) := by
    have hDcomp := (hη.continuousOn_fderiv_of_isOpen hs le_rfl).comp hline hmap
    exact hDcomp.clm_apply continuousOn_const
  exact (((continuousOn_const.mul (Complex.continuous_ofReal.pow n).continuousOn).smul
    hform).add <| (Complex.continuous_ofReal.pow (n + 1)).continuousOn.smul hDf)

omit [Nontrivial E] in
/-- Derivative in the dilation parameter of the pullback of a form. -/
theorem radialPullback_hasDerivAt (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (x : E) (t : ℝ)
    (hη : DifferentiableAt ℂ η ((t : ℂ) • x)) :
    HasDerivAt (radialPullback n η x)
      (radialPullbackDeriv n η x t) t := by
  have hi : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hline : HasDerivAt (fun s : ℝ ↦ (s : ℂ) • x) x t := by
    simpa only [one_smul] using hi.smul_const x
  have hform : HasDerivAt (fun s : ℝ ↦ η ((s : ℂ) • x))
      (fderiv ℂ η ((t : ℂ) • x) x) t := by
    have hf := hη.hasFDerivAt.restrictScalars ℝ
    simpa only [Function.comp_apply] using!
      hf.comp_hasDerivAt t hline
  have hpow : HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ (n + 1))
      (((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n) t := by
    simpa only [Pi.pow_apply, Nat.add_sub_cancel, mul_one] using! hi.pow (n + 1)
  simpa only [radialPullback, radialPullbackDeriv, Pi.smul_apply, add_comm] using!
    hpow.smul hform

omit [Nontrivial E] in
lemma continuous_extDeriv (n : ℕ)
    (η : E → E [⋀^Fin n]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η) :
    Continuous (extDeriv η) := by
  change Continuous fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℂ η x)
  convert (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ E ℂ).continuous.comp
    (hη.continuous_fderiv one_ne_zero) using 1
  exact funext fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply _

omit [Nontrivial E] in
lemma continuousOn_extDeriv (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin n]→L[ℂ] ℂ) (hs : IsOpen s) (hη : ContDiffOn ℂ 1 η s) :
    ContinuousOn (extDeriv η) s := by
  change ContinuousOn (fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℂ η x)) s
  have h := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ E ℂ).continuous.comp_continuousOn
    (hη.continuousOn_fderiv_of_isOpen hs le_rfl)
  convert h using 1
  exact funext fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply _

omit [Nontrivial E] in
/-- The integral of the derivative of the dilation pullback is evaluation at dilation one. -/
theorem integral_radialPullbackDeriv (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η) (x : E) :
    (∫ t : ℝ in 0..1, radialPullbackDeriv n η x t) = η x := by
  have hint : IntervalIntegrable (radialPullbackDeriv n η x) MeasureTheory.volume
      (0 : ℝ) 1 := (continuous_radialPullbackDeriv n η hη x).continuousOn.intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := radialPullback n η x) (f' := radialPullbackDeriv n η x)
    (fun t _ ↦ radialPullback_hasDerivAt n η x t
      (hη.differentiable one_ne_zero ((t : ℂ) • x)))
    hint
  have hzero : radialPullback n η x 0 = 0 := by
    ext v
    simp [radialPullback]
  have hone : radialPullback n η x 1 = η x := by
    ext v
    simp [radialPullback]
  rwa [hzero, hone, sub_zero] at h

omit [Nontrivial E] in
/-- The fundamental theorem of calculus for radial pullback, assuming smoothness only on the
star-convex domain containing the radial segment. -/
theorem integral_radialPullbackDeriv_of_contDiffOn (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s) {x : E} (hx : x ∈ s) :
    (∫ t : ℝ in 0..1, radialPullbackDeriv n η x t) = η x := by
  have hint : IntervalIntegrable (radialPullbackDeriv n η x) MeasureTheory.volume
      (0 : ℝ) 1 :=
    (continuousOn_radialPullbackDeriv n η hs hstar hη hx).intervalIntegrable_of_Icc (by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := radialPullback n η x) (f' := radialPullbackDeriv n η x)
    (fun t ht ↦ radialPullback_hasDerivAt n η x t <|
      (hη.contDiffAt (hs.mem_nhds (smul_mem_of_starConvex_zero hstar hx <| by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))).differentiableAt one_ne_zero)
    hint
  have hzero : radialPullback n η x 0 = 0 := by
    ext v
    simp [radialPullback]
  have hone : radialPullback n η x 1 = η x := by
    ext v
    simp [radialPullback]
  rwa [hzero, hone, sub_zero] at h

omit [Nontrivial E] in
/-- The radial chain-homotopy identity on a finite-dimensional complex normed space. -/
theorem extDeriv_radialHomotopy_add [FiniteDimensional ℂ E] (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η) (x : E) :
    extDeriv (radialHomotopy n η) x + radialHomotopy (n + 1) (extDeriv η) x = η x := by
  have hB : Continuous fun t : ℝ ↦ radialIntegrand (n + 1) (extDeriv η) t x :=
    (continuous_radialIntegrand (n + 1) (extDeriv η) (continuous_extDeriv (n + 1) η hη)).comp
      (continuous_const.prodMk continuous_id)
  have hA : Continuous fun t : ℝ ↦ extDeriv (radialIntegrand n η t) x := by
    apply ((continuous_radialPullbackDeriv n η hη x).sub hB).congr
    intro t
    have hc : extDeriv (radialIntegrand n η t) x +
        radialIntegrand (n + 1) (extDeriv η) t x = radialPullbackDeriv n η x t := by
      simpa only [radialPullbackDeriv] using
        extDeriv_radialIntegrand_add n η t x
          (hη.differentiable one_ne_zero ((t : ℂ) • x))
    change radialPullbackDeriv n η x t -
      radialIntegrand (n + 1) (extDeriv η) t x = extDeriv (radialIntegrand n η t) x
    rw [← hc]
    abel
  rw [extDeriv_radialHomotopy n η hη x]
  change (∫ t : ℝ in 0..1, extDeriv (radialIntegrand n η t) x) +
    (∫ t : ℝ in 0..1, radialIntegrand (n + 1) (extDeriv η) t x) = η x
  rw [← intervalIntegral.integral_add hA.continuousOn.intervalIntegrable
    hB.continuousOn.intervalIntegrable]
  calc
    (∫ t : ℝ in 0..1,
        extDeriv (radialIntegrand n η t) x + radialIntegrand (n + 1) (extDeriv η) t x) =
        ∫ t : ℝ in 0..1, radialPullbackDeriv n η x t := by
          apply intervalIntegral.integral_congr
          intro t _
          exact extDeriv_radialIntegrand_add n η t x
            (hη.differentiable one_ne_zero ((t : ℂ) • x))
    _ = η x := integral_radialPullbackDeriv n η hη x

omit [Nontrivial E] in
/-- The radial chain-homotopy identity on an open set star-convex about the origin.  The total
function representing the form is required to be smooth only on that set. -/
theorem extDeriv_radialHomotopy_add_of_contDiffOn [FiniteDimensional ℂ E] (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s) {x : E} (hx : x ∈ s) :
    extDeriv (radialHomotopy n η) x + radialHomotopy (n + 1) (extDeriv η) x = η x := by
  have hB : ContinuousOn (fun t : ℝ ↦ radialIntegrand (n + 1) (extDeriv η) t x)
      (Set.Icc 0 1) := by
    have h := (continuousOn_radialIntegrand (n + 1) (extDeriv η) hstar
      (continuousOn_extDeriv (n + 1) η hs hη)).comp
        (continuousOn_const.prodMk continuousOn_id) (fun t ht ↦ ⟨hx, ht⟩)
    simpa only [Function.comp_def, id_eq] using h
  have hA : ContinuousOn (fun t : ℝ ↦ extDeriv (radialIntegrand n η t) x)
      (Set.Icc 0 1) := by
    apply ((continuousOn_radialPullbackDeriv n η hs hstar hη hx).sub hB).congr
    intro t ht
    have hc : extDeriv (radialIntegrand n η t) x +
        radialIntegrand (n + 1) (extDeriv η) t x = radialPullbackDeriv n η x t := by
      simpa only [radialPullbackDeriv] using
        extDeriv_radialIntegrand_add n η t x <|
          (hη.contDiffAt (hs.mem_nhds (smul_mem_of_starConvex_zero hstar hx ht))).differentiableAt
            one_ne_zero
    change extDeriv (radialIntegrand n η t) x = radialPullbackDeriv n η x t -
      radialIntegrand (n + 1) (extDeriv η) t x
    rw [← hc]
    abel
  rw [extDeriv_radialHomotopy_of_contDiffOn n η hs hstar hη hx]
  change (∫ t : ℝ in 0..1, extDeriv (radialIntegrand n η t) x) +
    (∫ t : ℝ in 0..1, radialIntegrand (n + 1) (extDeriv η) t x) = η x
  rw [← intervalIntegral.integral_add
    (hA.intervalIntegrable_of_Icc (by norm_num)) (hB.intervalIntegrable_of_Icc (by norm_num))]
  calc
    (∫ t : ℝ in 0..1,
        extDeriv (radialIntegrand n η t) x + radialIntegrand (n + 1) (extDeriv η) t x) =
        ∫ t : ℝ in 0..1, radialPullbackDeriv n η x t := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
          exact extDeriv_radialIntegrand_add n η t x <|
            (hη.contDiffAt
              (hs.mem_nhds (smul_mem_of_starConvex_zero hstar hx ht'))).differentiableAt
                one_ne_zero
    _ = η x := integral_radialPullbackDeriv_of_contDiffOn n η hs hstar hη hx

omit [Nontrivial E] in
/-- Local Poincaré lemma in positive degree on an open set star-convex about the origin. -/
theorem extDeriv_radialHomotopy_of_closedOn [FiniteDimensional ℂ E] (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s)
    (hclosed : Set.EqOn (extDeriv η) 0 s) :
    Set.EqOn (extDeriv (radialHomotopy n η)) η s := by
  intro x hx
  have hzero : radialHomotopy (n + 1) (extDeriv η) x = 0 := by
    change (∫ t : ℝ in 0..1, radialIntegrand (n + 1) (extDeriv η) t x) = 0
    calc
      (∫ t : ℝ in 0..1, radialIntegrand (n + 1) (extDeriv η) t x) =
          ∫ _t : ℝ in 0..1, 0 := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
            change ((t : ℂ) ^ (n + 1)) •
              (extDeriv η ((t : ℂ) • x)).curryLeft x = 0
            rw [hclosed (smul_mem_of_starConvex_zero hstar hx ht')]
            simp
      _ = 0 := by simp
  have h := extDeriv_radialHomotopy_add_of_contDiffOn n η hs hstar hη hx
  rwa [hzero, add_zero] at h

omit [Nontrivial E] in
/-- A closed positive-degree form on an open star-convex set has the explicit radial primitive,
which is itself continuously differentiable on that set. -/
theorem exists_contDiffOn_primitive_of_closedOn [FiniteDimensional ℂ E] (n : ℕ) {s : Set E}
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s)
    (hclosed : Set.EqOn (extDeriv η) 0 s) :
    ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
      ContDiffOn ℂ 1 θ s ∧ Set.EqOn (extDeriv θ) η s :=
  ⟨radialHomotopy n η, radialHomotopy_contDiffOn_one n η hs hstar hη,
    extDeriv_radialHomotopy_of_closedOn n η hs hstar hη hclosed⟩

omit [Nontrivial E] in
/-- Open-ball form of the local positive-degree Poincaré lemma. -/
theorem exists_contDiffOn_primitive_on_ball [FiniteDimensional ℂ E] (n : ℕ) {r : ℝ}
    (hr : 0 < r) (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hη : ContDiffOn ℂ 1 η (Metric.ball 0 r))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball 0 r)) :
    ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
      ContDiffOn ℂ 1 θ (Metric.ball 0 r) ∧
        Set.EqOn (extDeriv θ) η (Metric.ball 0 r) :=
  exists_contDiffOn_primitive_of_closedOn n η Metric.isOpen_ball
    ((convex_ball (0 : E) r).starConvex (Metric.mem_ball_self hr)) hη hclosed

/-- The scalar coefficient of a differential `0`-form. -/
def zeroFormCoeff (η : E → E [⋀^Fin 0]→L[ℂ] ℂ) (x : E) : ℂ := η x 0

omit [Nontrivial E] in
/-- Every differential `0`-form is the constant alternating map associated to its unique scalar
coefficient. -/
lemma zeroForm_eq_constOfIsEmpty (η : E → E [⋀^Fin 0]→L[ℂ] ℂ) :
    η = fun x ↦ ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) (zeroFormCoeff η x) := by
  funext x
  ext v
  obtain rfl : v = 0 := Subsingleton.elim _ _
  rfl

omit [Nontrivial E] in
/-- The degree-zero part of the local Poincaré lemma: a closed `0`-form on an open set
star-convex about the origin is constant there. -/
theorem zeroForm_eq_at_zero_of_closedOn {s : Set E}
    (η : E → E [⋀^Fin 0]→L[ℂ] ℂ) (hs : IsOpen s)
    (hstar : StarConvex ℝ 0 s) (hη : ContDiffOn ℂ 1 η s)
    (hclosed : Set.EqOn (extDeriv η) 0 s) :
    Set.EqOn η (fun _ ↦ η 0) s := by
  let f : E → ℂ := zeroFormCoeff η
  have hηrepr : η = fun y ↦ ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) (f y) :=
    zeroForm_eq_constOfIsEmpty η
  have hfderiv_zero {y : E} (hy : y ∈ s) : fderiv ℂ f y = 0 := by
    have hform := hclosed hy
    rw [hηrepr, extDeriv_constOfIsEmpty] at hform
    ext v
    have hv := congrArg (fun L : E [⋀^Fin 1]→L[ℂ] ℂ ↦ L (fun _ ↦ v)) hform
    simpa using hv
  intro x hx
  have hcoeff : f x = f 0 := by
    have hzero_mem : (0 : E) ∈ s := by
      simpa using smul_mem_of_starConvex_zero hstar hx
        (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
        HasDerivAt (fun r : ℝ ↦ f ((r : ℂ) • x)) 0 t := by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have htx : (t : ℂ) • x ∈ s := smul_mem_of_starConvex_zero hstar hx ht'
      have hηat : DifferentiableAt ℂ η ((t : ℂ) • x) :=
        (hη.contDiffAt (hs.mem_nhds htx)).differentiableAt one_ne_zero
      have hfat : DifferentiableAt ℂ f ((t : ℂ) • x) := by
        change DifferentiableAt ℂ (fun y ↦ η y 0) ((t : ℂ) • x)
        exact hηat.continuousAlternatingMap_apply_const 0
      have hi : HasDerivAt (fun r : ℝ ↦ (r : ℂ)) 1 t := by
        simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
          Complex.ofRealCLM.hasFDerivAt.hasDerivAt
      have hline : HasDerivAt (fun r : ℝ ↦ (r : ℂ) • x) x t := by
        simpa only [one_smul] using hi.smul_const x
      have hf := hfat.hasFDerivAt.restrictScalars ℝ
      rw [hfderiv_zero htx] at hf
      simpa only [Function.comp_apply, zero_apply] using!
        hf.comp_hasDerivAt t hline
    have hint : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℂ)) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (f := fun t : ℝ ↦ f ((t : ℂ) • x))
      (f' := fun _ : ℝ ↦ (0 : ℂ)) hderiv hint
    exact sub_eq_zero.mp (by simpa using hfund.symm)
  rw [hηrepr]
  exact congrArg (ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0)) hcoeff

omit [Nontrivial E] in
/-- Global degree-zero Poincaré lemma: a closed continuously differentiable `0`-form is constant. -/
theorem zeroForm_eq_at_zero_of_closed
    (η : E → E [⋀^Fin 0]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η)
    (hclosed : extDeriv η = 0) : η = fun _ ↦ η 0 := by
  funext x
  exact zeroForm_eq_at_zero_of_closedOn η isOpen_univ
    (convex_univ.starConvex (Set.mem_univ 0)) hη.contDiffOn
    (fun _ _ ↦ by rw [hclosed]) (Set.mem_univ x)

omit [Nontrivial E] in
/-- Global Poincaré lemma in positive degree on a finite-dimensional complex normed space. -/
theorem extDeriv_radialHomotopy_of_closed [FiniteDimensional ℂ E] (n : ℕ)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (hη : ContDiff ℂ 1 η)
    (hclosed : extDeriv η = 0) :
    extDeriv (radialHomotopy n η) = η := by
  funext x
  have h := extDeriv_radialHomotopy_add n η hη x
  rw [hclosed] at h
  simpa [radialHomotopy, radialIntegrand] using h

end DifferentialForm
