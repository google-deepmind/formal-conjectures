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

public import FormalConjecturesForMathlib.Mathlib.Analysis.Calculus.DifferentialForm.Poincare

import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The holomorphic Poincaré lemma on a ball

Integration over the real radial parameter preserves complex analyticity. This is proved directly:
the radial homotopy operator of `Poincare` applied to a form given by a convergent formal
multilinear series is again given by such a series, obtained by integrating the homogeneous terms.

Consequently a closed analytic differential form on a ball has an analytic primitive there, and
translating the ball to the origin gives the same statement about a ball centred anywhere.
-/

@[expose] public noncomputable section

open ContinuousAlternatingMap MeasureTheory
open scoped ContDiff Interval

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]

/-- The formal power series of the radial primitive. -/
def radialPrimitiveSeries (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) :
    FormalMultilinearSeries ℂ E (E [⋀^Fin n]→L[ℂ] ℂ) :=
  letI : SeminormedAddCommGroup (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  fun
  | 0 => 0
  | k + 1 =>
      (continuousMultilinearCurryRightEquiv' ℂ k E (E [⋀^Fin n]→L[ℂ] ℂ)).symm
        (((k + n + 1 : ℕ) : ℂ)⁻¹ •
          ContinuousLinearMap.compContinuousMultilinearMap
            (ContinuousAlternatingMap.curryLeftLI
              (n := n) (𝕜 := ℂ) (E := E) (F := ℂ)).toContinuousLinearMap (p k))

omit [Nontrivial E] in
@[simp] lemma radialPrimitiveSeries_zero (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) :
    radialPrimitiveSeries n p 0 = 0 := rfl

omit [Nontrivial E] in
@[simp] lemma radialPrimitiveSeries_succ_apply (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (k : ℕ) (x : E) :
    radialPrimitiveSeries n p (k + 1) (fun _ ↦ x) =
      ((k + n + 1 : ℕ) : ℂ)⁻¹ • (p k (fun _ ↦ x)).curryLeft x := by
  simp [radialPrimitiveSeries]
  congr 2

omit [Nontrivial E] in
lemma norm_radialPrimitiveSeries_succ_le (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) (k : ℕ) :
    ‖radialPrimitiveSeries n p (k + 1)‖ ≤ ‖p k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg (p k)) fun v ↦ ?_
  rw [radialPrimitiveSeries, continuousMultilinearCurryRightEquiv_symm_apply']
  simp only [_root_.smul_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply]
  calc
    ‖(((k + n + 1 : ℕ) : ℂ)⁻¹) • (p k (Fin.init v)).curryLeft (v (Fin.last k))‖ ≤
        ‖((k + n + 1 : ℕ) : ℂ)⁻¹‖ *
          ‖(p k (Fin.init v)).curryLeft (v (Fin.last k))‖ := by
      change ‖((((k + n + 1 : ℕ) : ℂ)⁻¹) •
          (p k (Fin.init v)).curryLeft (v (Fin.last k))).toContinuousMultilinearMap‖ ≤
        ‖((k + n + 1 : ℕ) : ℂ)⁻¹‖ *
          ‖((p k (Fin.init v)).curryLeft (v (Fin.last k))).toContinuousMultilinearMap‖
      rw [ContinuousAlternatingMap.toContinuousMultilinearMap_smul]
      exact ContinuousMultilinearMap.opNorm_smul_le _ _
    _ ≤ 1 * (‖p k (Fin.init v)‖ * ‖v (Fin.last k)‖) := by
      refine mul_le_mul ?_ ?_ (norm_nonneg _) zero_le_one
      · rw [norm_inv, norm_natCast]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (k + n)))
      · simpa only [ContinuousAlternatingMap.norm_curryLeft] using
          (p k (Fin.init v)).curryLeft.le_opNorm (v (Fin.last k))
    _ ≤ ‖p k‖ * ((∏ i : Fin k, ‖v (Fin.castSucc i)‖) * ‖v (Fin.last k)‖) := by
      rw [one_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa only [Fin.init_def] using ContinuousMultilinearMap.le_opNorm (p k) (Fin.init v)
    _ = ‖p k‖ * ∏ i : Fin (k + 1), ‖v i‖ := by
      rw [Fin.prod_univ_castSucc]

omit [Nontrivial E] in
lemma radius_le_radius_radialPrimitiveSeries (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) :
    p.radius ≤ (radialPrimitiveSeries n p).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr₀ hr ↦ ?_
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine (summable_nat_add_iff
    (f := fun m ↦ ‖radialPrimitiveSeries n p m‖ * (r : ℝ) ^ m) 1).mp ?_
  exact ((p.summable_norm_mul_pow hr).mul_left (r : ℝ)).of_nonneg_of_le
    (fun _ ↦ by positivity) (fun k ↦ by
      change ‖radialPrimitiveSeries n p (k + 1)‖ * (r : ℝ) ^ (k + 1) ≤
        (r : ℝ) * (‖p k‖ * (r : ℝ) ^ k)
      rw [pow_succ]
      calc
        ‖radialPrimitiveSeries n p (k + 1)‖ * ((r : ℝ) ^ k * r) ≤
            ‖p k‖ * ((r : ℝ) ^ k * r) := by
              gcongr
              exact norm_radialPrimitiveSeries_succ_le n p k
        _ = (r : ℝ) * (‖p k‖ * (r : ℝ) ^ k) := by ring)

omit [Nontrivial E] in
/-- The formal radial primitive has positive convergence radius whenever the original series does. -/
lemma radialPrimitiveSeries_radius_pos (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (hp : 0 < p.radius) : 0 < (radialPrimitiveSeries n p).radius :=
  hp.trans_le (radius_le_radius_radialPrimitiveSeries n p)

omit [Nontrivial E] in
/-- The sum of the formal radial primitive is analytic throughout the convergence ball of the
original differential form. -/
theorem analyticOnNhd_radialPrimitiveSeries_sum (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (hp : 0 < p.radius) :
    AnalyticOnNhd ℂ (radialPrimitiveSeries n p).sum (Metric.eball 0 p.radius) :=
  ((radialPrimitiveSeries n p).hasFPowerSeriesOnBall
    (radialPrimitiveSeries_radius_pos n p hp)).analyticOnNhd.mono
    (Metric.eball_subset_eball (radius_le_radius_radialPrimitiveSeries n p))

/-- The real interval integral of a complex monomial. -/
lemma intervalIntegral_ofReal_pow (m : ℕ) :
    (∫ t : ℝ in 0..1, (t : ℂ) ^ m) = (((m + 1 : ℕ) : ℂ)⁻¹) := by
  have hderiv (t : ℝ) : HasDerivAt
      (fun s : ℝ ↦ (((m + 1 : ℕ) : ℂ)⁻¹) * (s : ℂ) ^ (m + 1))
      ((t : ℂ) ^ m) t := by
    have h : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
        Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    have hn : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    convert (h.pow (m + 1)).const_mul (((m + 1 : ℕ) : ℂ)⁻¹) using 1
    all_goals first | rfl | (rw [Nat.add_sub_cancel, mul_one, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul])
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ ↦ hderiv t)
    ((Complex.continuous_ofReal.pow m).intervalIntegrable 0 1)

/-- Integrating a complex monomial times a fixed vector gives the same scalar factor. -/
lemma intervalIntegral_ofReal_pow_smul
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (m : ℕ) (v : G) :
    (∫ t : ℝ in 0..1, ((t : ℂ) ^ m) • v) = (((m + 1 : ℕ) : ℂ)⁻¹) • v := by
  rw [intervalIntegral.integral_smul_const, intervalIntegral_ofReal_pow]

omit [Nontrivial E] in
/-- On the convergence ball, the sum of the primitive series is the expected series of contracted
homogeneous coefficients. -/
lemma radialPrimitiveSeries_sum_eq_tsum (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    {x : E} (hx : x ∈ Metric.eball 0 p.radius) :
    (radialPrimitiveSeries n p).sum x =
      ∑' k : ℕ, ((k + n + 1 : ℕ) : ℂ)⁻¹ • (p k (fun _ ↦ x)).curryLeft x := by
  have hx' : x ∈ Metric.eball 0 (radialPrimitiveSeries n p).radius :=
    Metric.eball_subset_eball (radius_le_radius_radialPrimitiveSeries n p) hx
  have hsum := (radialPrimitiveSeries n p).summable hx'
  rw [FormalMultilinearSeries.sum, ← hsum.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, radialPrimitiveSeries_zero,
    zero_apply, zero_add]
  exact tsum_congr fun k ↦ radialPrimitiveSeries_succ_apply n p k x

omit [Nontrivial E] in
/-- The homogeneous expansion of a form can be contracted term by term along a real radial
segment. -/
lemma hasSum_radialIntegrand_of_hasFPowerSeriesOnBall (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) {x : E} (hx : x ∈ Metric.eball 0 R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun k : ℕ ↦ ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x)
      (radialIntegrand n η t x) := by
  have htNorm : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  have htx : (t : ℂ) • x ∈ Metric.eball (0 : E) R := by
    rw [mem_eball_zero_iff] at hx ⊢
    rw [enorm_smul]
    have htEnorm : ‖(t : ℂ)‖ₑ ≤ 1 := by
      rw [enorm_eq_nnnorm, ENNReal.coe_le_one_iff]
      exact NNReal.coe_le_coe.mp (by simpa using htNorm)
    exact (by simpa [mul_comm] using
      (mul_le_mul_right htEnorm ‖x‖ₑ).trans_lt (by simpa using hx))
  let contraction : (E [⋀^Fin (n + 1)]→L[ℂ] ℂ) →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ) :=
    (ContinuousLinearMap.apply ℂ (E [⋀^Fin n]→L[ℂ] ℂ) x).comp
      (ContinuousAlternatingMap.curryLeftLI
        (n := n) (𝕜 := ℂ) (E := E) (F := ℂ)).toContinuousLinearMap
  have hs := (hp.hasSum htx).mapL contraction
  have hst := hs.const_smul ((t : ℂ) ^ n)
  have hst' : HasSum (fun k ↦ ((t : ℂ) ^ n) •
      contraction (p k (fun _ ↦ (t : ℂ) • x)))
      (((t : ℂ) ^ n) • (η ((t : ℂ) • x)).curryLeft x) := by
    simpa [contraction] using hst
  refine HasSum.congr_fun hst' (fun k ↦ ?_)
  change ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x =
    ((t : ℂ) ^ n) • (p k (fun _ ↦ (t : ℂ) • x)).curryLeft x
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  change (t : ℂ) ^ (k + n) * (p k (fun _ ↦ x)).curryLeft x v =
    (t : ℂ) ^ n * ((t : ℂ) ^ k * (p k (fun _ ↦ x)).curryLeft x v)
  rw [← mul_assoc, ← pow_add, add_comm n k]

omit [Nontrivial E] in
/-- The homogeneous expansion of a form may be integrated term by term along a real radial
segment. -/
lemma hasSum_intervalIntegral_radialTerms_of_hasFPowerSeriesOnBall (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) {x : E} (hx : x ∈ Metric.eball 0 R) :
    HasSum (fun k : ℕ ↦ ∫ t : ℝ in 0..1,
        ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x)
      (radialHomotopy n η x) := by
  let F : ℕ → ℝ → (E [⋀^Fin n]→L[ℂ] ℂ) := fun k t ↦
    ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x
  let bound : ℕ → ℝ → ℝ := fun k _ ↦ ‖p k (fun _ ↦ x)‖ * ‖x‖
  refine intervalIntegral.hasSum_integral_of_dominated_convergence bound (fun k ↦ ?_)
    (fun k ↦ ?_) ?_ ?_ ?_
  · exact ((Complex.continuous_ofReal.pow (k + n)).smul continuous_const).aestronglyMeasurable
  · filter_upwards [] with t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have htNorm : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
      exact ht.2
    have hpow : ‖(t : ℂ) ^ (k + n)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) htNorm
    have hsmul : ‖((t : ℂ) ^ (k + n) • (p k (fun _ ↦ x)).curryLeft x)‖ ≤
        ‖(t : ℂ) ^ (k + n)‖ * ‖(p k (fun _ ↦ x)).curryLeft x‖ := by
      change ‖(((t : ℂ) ^ (k + n) •
          (p k (fun _ ↦ x)).curryLeft x).toContinuousMultilinearMap)‖ ≤
        ‖(t : ℂ) ^ (k + n)‖ *
          ‖((p k (fun _ ↦ x)).curryLeft x).toContinuousMultilinearMap‖
      rw [ContinuousAlternatingMap.toContinuousMultilinearMap_smul]
      exact ContinuousMultilinearMap.opNorm_smul_le _ _
    exact hsmul.trans <| calc
      ‖(t : ℂ) ^ (k + n)‖ * ‖(p k (fun _ ↦ x)).curryLeft x‖ ≤
          1 * (‖p k (fun _ ↦ x)‖ * ‖x‖) := by
        refine mul_le_mul hpow ?_ (norm_nonneg _) zero_le_one
        simpa only [ContinuousAlternatingMap.norm_curryLeft] using
          (p k (fun _ ↦ x)).curryLeft.le_opNorm x
      _ = bound k t := by simp [bound]
  · filter_upwards [] with t ht
    exact ((p.summable_norm_apply
      (Metric.eball_subset_eball hp.r_le hx)).mul_right ‖x‖)
  · simp [bound]
  · filter_upwards [] with t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hasSum_radialIntegrand_of_hasFPowerSeriesOnBall n p η hp hx ⟨ht.1.le, ht.2⟩

omit [Nontrivial E] in
/-- On a power-series ball, the radial homotopy is exactly the sum of the formal primitive series. -/
theorem radialHomotopy_eq_radialPrimitiveSeries_sum (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) {x : E} (hx : x ∈ Metric.eball 0 R) :
    radialHomotopy n η x = (radialPrimitiveSeries n p).sum x := by
  have hs := hasSum_intervalIntegral_radialTerms_of_hasFPowerSeriesOnBall n p η hp hx
  have hs' : HasSum (fun k : ℕ ↦
      (((k + n + 1 : ℕ) : ℂ)⁻¹) • (p k (fun _ ↦ x)).curryLeft x)
      (radialHomotopy n η x) := HasSum.congr_fun hs fun k ↦
    (intervalIntegral_ofReal_pow_smul (k + n) ((p k (fun _ ↦ x)).curryLeft x)).symm
  calc
    radialHomotopy n η x = ∑' k : ℕ,
        (((k + n + 1 : ℕ) : ℂ)⁻¹) • (p k (fun _ ↦ x)).curryLeft x := hs'.tsum_eq.symm
    _ = (radialPrimitiveSeries n p).sum x :=
      (radialPrimitiveSeries_sum_eq_tsum n p
        (Metric.eball_subset_eball hp.r_le hx)).symm

omit [Nontrivial E] in
/-- Integrating a complex-analytic differential form over the real radial parameter preserves
complex analyticity. -/
theorem analyticOnNhd_radialHomotopy_of_hasFPowerSeriesOnBall (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) :
    AnalyticOnNhd ℂ (radialHomotopy n η) (Metric.eball 0 R) :=
  AnalyticOnNhd.congr Metric.isOpen_eball
    ((analyticOnNhd_radialPrimitiveSeries_sum n p hp.radius_pos).mono
      (Metric.eball_subset_eball hp.r_le))
    fun _ hx ↦ (radialHomotopy_eq_radialPrimitiveSeries_sum n p η hp hx).symm

omit [Nontrivial E] in
/-- The analytic Poincaré lemma on a complex normed-space ball. The primitive is the explicit
radial homotopy, and no exactness assumption is used. -/
theorem exists_analyticOnNhd_primitive_on_ball_of_hasFPowerSeriesOnBall
    [FiniteDimensional ℂ E] (n : ℕ) {r : NNReal} (hr : 0 < r)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hp : HasFPowerSeriesOnBall η p 0 (r : ENNReal))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball 0 (r : ℝ))) :
    ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
      AnalyticOnNhd ℂ θ (Metric.ball 0 (r : ℝ)) ∧
        Set.EqOn (extDeriv θ) η (Metric.ball 0 (r : ℝ)) := by
  have hηanalytic : AnalyticOnNhd ℂ η (Metric.ball 0 (r : ℝ)) := by
    simpa only [Metric.eball_coe] using hp.analyticOnNhd
  have hη : ContDiffOn ℂ 1 η (Metric.ball 0 (r : ℝ)) :=
    hηanalytic.contDiffOn Metric.isOpen_ball.uniqueDiffOn
  refine ⟨radialHomotopy n η, ?_,
    extDeriv_radialHomotopy_of_closedOn n η Metric.isOpen_ball
      ((convex_ball (0 : E) (r : ℝ)).starConvex (Metric.mem_ball_self (by exact_mod_cast hr)))
      hη hclosed⟩
  simpa only [Metric.eball_coe] using
    analyticOnNhd_radialHomotopy_of_hasFPowerSeriesOnBall n p η hp

omit [Nontrivial E] in
/-- The analytic Poincaré lemma after shrinking an arbitrary analytic ball around the origin.
The smaller radius is chosen inside both the original ball and the convergence ball of the power
series of the form at the origin. -/
theorem exists_analyticOnNhd_primitive_on_smaller_ball
    [FiniteDimensional ℂ E] (n : ℕ) {r : ℝ} (hr : 0 < r)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hη : AnalyticOnNhd ℂ η (Metric.ball 0 r))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball 0 r)) :
    ∃ ρ : NNReal, 0 < ρ ∧ (ρ : ℝ) < r ∧
      ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
        AnalyticOnNhd ℂ θ (Metric.ball 0 (ρ : ℝ)) ∧
          Set.EqOn (extDeriv θ) η (Metric.ball 0 (ρ : ℝ)) := by
  have hzero : (0 : E) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  obtain ⟨p, R, hp⟩ := hη 0 hzero
  have hrENN : 0 < (Real.toNNReal r : ENNReal) := by
    simpa only [ENNReal.coe_pos, Real.toNNReal_pos] using hr
  have hmin : 0 < min (Real.toNNReal r : ENNReal) R := lt_min hrENN hp.r_pos
  obtain ⟨ρ, hρpos, hρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hmin
  have hρR : (ρ : ENNReal) ≤ R :=
    le_trans hρ.le (min_le_right (Real.toNNReal r : ENNReal) R)
  have hρr : (ρ : ℝ) < r := by
    have hlt : (ρ : ENNReal) < (Real.toNNReal r : ENNReal) :=
      hρ.trans_le (min_le_left (Real.toNNReal r : ENNReal) R)
    have hlt' : (ρ : ℝ) < (Real.toNNReal r : ℝ) := by exact_mod_cast ENNReal.coe_lt_coe.mp hlt
    simpa only [Real.coe_toNNReal r hr.le] using hlt'
  exact ⟨ρ, by exact_mod_cast hρpos, hρr,
    exists_analyticOnNhd_primitive_on_ball_of_hasFPowerSeriesOnBall n
      (by exact_mod_cast hρpos) p η (hp.mono (by exact_mod_cast hρpos) hρR)
      (hclosed.mono (Metric.ball_subset_ball hρr.le))⟩

omit [Nontrivial E] in
/-- Translate the base point of a differential form field to the origin. -/
def translateForm {p : ℕ} (c : E) (A : E → E [⋀^Fin p]→L[ℂ] ℂ) :
    E → E [⋀^Fin p]→L[ℂ] ℂ := fun x ↦ A (c + x)

omit [Nontrivial E] in
lemma fderiv_translateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (c + x)) :
    fderiv ℂ (translateForm c A) x = fderiv ℂ A (c + x) := by
  have ht : HasFDerivAt (fun y : E ↦ c + y) (ContinuousLinearMap.id ℂ E) x :=
    (hasFDerivAt_id x).const_add c
  exact (hA.hasFDerivAt.comp x ht).fderiv.trans (ContinuousLinearMap.comp_id _)

omit [Nontrivial E] in
lemma extDeriv_translateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (c + x)) :
    extDeriv (translateForm c A) x = extDeriv A (c + x) := by
  rw [extDeriv, extDeriv, fderiv_translateForm c A x hA]

omit [Nontrivial E] [NormedSpace ℂ E] in
lemma add_mem_ball_iff (c x : E) (r : ℝ) :
    c + x ∈ Metric.ball c r ↔ x ∈ Metric.ball 0 r := by
  simp [Metric.mem_ball, dist_eq_norm]

omit [Nontrivial E] in
lemma analyticOnNhd_translateForm {p : ℕ} (c : E) (r : ℝ)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ)
    (hA : AnalyticOnNhd ℂ A (Metric.ball c r)) :
    AnalyticOnNhd ℂ (translateForm c A) (Metric.ball 0 r) :=
  hA.comp (analyticOnNhd_const.add analyticOnNhd_id) fun x hx ↦
    (add_mem_ball_iff c x r).2 hx

omit [Nontrivial E] in
/-- Translate a differential form field from origin-centered coordinates back to a center. -/
def untranslateForm {p : ℕ} (c : E) (A : E → E [⋀^Fin p]→L[ℂ] ℂ) :
    E → E [⋀^Fin p]→L[ℂ] ℂ := fun x ↦ A (x - c)

omit [Nontrivial E] in
lemma fderiv_untranslateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (x - c)) :
    fderiv ℂ (untranslateForm c A) x = fderiv ℂ A (x - c) := by
  have ht : HasFDerivAt (fun y : E ↦ y - c) (ContinuousLinearMap.id ℂ E) x :=
    hasFDerivAt_sub_const c
  exact (hA.hasFDerivAt.comp x ht).fderiv.trans (ContinuousLinearMap.comp_id _)

omit [Nontrivial E] in
lemma extDeriv_untranslateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (x - c)) :
    extDeriv (untranslateForm c A) x = extDeriv A (x - c) := by
  rw [extDeriv, extDeriv, fderiv_untranslateForm c A x hA]

omit [Nontrivial E] [NormedSpace ℂ E] in
lemma mem_ball_iff_sub_mem_ball (c x : E) (r : ℝ) :
    x ∈ Metric.ball c r ↔ x - c ∈ Metric.ball 0 r := by
  simp [Metric.mem_ball, dist_eq_norm]

omit [Nontrivial E] in
lemma analyticOnNhd_untranslateForm {p : ℕ} (c : E) (r : ℝ)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ)
    (hA : AnalyticOnNhd ℂ A (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (untranslateForm c A) (Metric.ball c r) :=
  hA.comp (analyticOnNhd_id.sub analyticOnNhd_const) fun x hx ↦
    (mem_ball_iff_sub_mem_ball c x r).1 hx

omit [Nontrivial E] in
/-- The analytic Poincaré lemma on a ball with arbitrary center, after shrinking the radius. -/
theorem exists_analyticOnNhd_primitive_on_smaller_centered_ball
    [FiniteDimensional ℂ E] (n : ℕ) {c : E} {r : ℝ} (hr : 0 < r)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hη : AnalyticOnNhd ℂ η (Metric.ball c r))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball c r)) :
    ∃ ρ : NNReal, 0 < ρ ∧ (ρ : ℝ) < r ∧
      ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
        AnalyticOnNhd ℂ θ (Metric.ball c (ρ : ℝ)) ∧
          Set.EqOn (extDeriv θ) η (Metric.ball c (ρ : ℝ)) := by
  let η₀ := translateForm c η
  have hη₀ : AnalyticOnNhd ℂ η₀ (Metric.ball 0 r) :=
    analyticOnNhd_translateForm c r η hη
  have hclosed₀ : Set.EqOn (extDeriv η₀) 0 (Metric.ball 0 r) := by
    intro x hx
    rw [extDeriv_translateForm c η x
      ((hη (c + x) ((add_mem_ball_iff c x r).2 hx)).differentiableAt)]
    exact hclosed ((add_mem_ball_iff c x r).2 hx)
  obtain ⟨ρ, hρ, hρr, θ₀, hθ₀, hprim⟩ :=
    exists_analyticOnNhd_primitive_on_smaller_ball n hr η₀ hη₀ hclosed₀
  refine ⟨ρ, hρ, hρr, untranslateForm c θ₀,
    analyticOnNhd_untranslateForm c (ρ : ℝ) θ₀ hθ₀, ?_⟩
  intro y hy
  have hy₀ : y - c ∈ Metric.ball 0 (ρ : ℝ) :=
    (mem_ball_iff_sub_mem_ball c y (ρ : ℝ)).1 hy
  rw [extDeriv_untranslateForm c θ₀ y ((hθ₀ (y - c) hy₀).differentiableAt),
    hprim hy₀]
  change η (c + (y - c)) = η y
  congr 1
  abel

omit [Nontrivial E] in
/-- A closed analytic zero-form is constant on a ball with arbitrary center. -/
theorem zeroForm_eq_at_center_of_closedOn_ball {c : E} {r : ℝ} (hr : 0 < r)
    (η : E → E [⋀^Fin 0]→L[ℂ] ℂ)
    (hη : AnalyticOnNhd ℂ η (Metric.ball c r))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball c r)) :
    Set.EqOn η (fun _ ↦ η c) (Metric.ball c r) := by
  let η₀ := translateForm c η
  have hη₀ : AnalyticOnNhd ℂ η₀ (Metric.ball 0 r) :=
    analyticOnNhd_translateForm c r η hη
  have hclosed₀ : Set.EqOn (extDeriv η₀) 0 (Metric.ball 0 r) := by
    intro x hx
    rw [extDeriv_translateForm c η x
      ((hη (c + x) ((add_mem_ball_iff c x r).2 hx)).differentiableAt)]
    exact hclosed ((add_mem_ball_iff c x r).2 hx)
  have hconst := zeroForm_eq_at_zero_of_closedOn η₀ Metric.isOpen_ball
    ((convex_ball (0 : E) r).starConvex (Metric.mem_ball_self hr))
    (hη₀.contDiffOn Metric.isOpen_ball.uniqueDiffOn : ContDiffOn ℂ 1 η₀ _) hclosed₀
  intro y hy
  have hy₀ : y - c ∈ Metric.ball 0 r := (mem_ball_iff_sub_mem_ball c y r).1 hy
  have h := hconst hy₀
  change η (c + (y - c)) = η (c + 0) at h
  simpa using h

end DifferentialForm
