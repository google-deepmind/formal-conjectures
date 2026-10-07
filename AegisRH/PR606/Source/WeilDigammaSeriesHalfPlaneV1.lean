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

import WeilDigammaSeriesRealV1
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic

/-!
AEGIS Ω — completion of Gauss's digamma series on the open right half-plane.

This module analytically continues the real-axis theorem from
`WeilDigammaSeriesRealV1` to every `z` with `0 < z.re`.  The series is
shown holomorphic by a local Weierstrass M-test using the exact rational
factorization

  1/(n+1) - 1/(z+n) = (z-1)/((n+1)(z+n)).

The identity theorem then transports the already-established positive-real-axis
identity to the full connected right half-plane.  Composing with the existing
`tsum_seriesTerm_eq_integral` theorem removes the remaining Gauss-digamma
integral dependency at source level.

AUTHORITY_EFFECT = NONE.
No RH conclusion is asserted here.
-/

open Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilDigammaSeriesHalfPlaneV1

open AEGIS.WeilDigammaIntegralReductionV1
open AEGIS.WeilDigammaSeriesRealV1

local notation "γ" => Real.eulerMascheroniConstant

def RightHalfPlaneV1 : Set ℂ := {z : ℂ | 0 < z.re}

theorem isOpen_rightHalfPlane_v1 : IsOpen RightHalfPlaneV1 := by
  exact Complex.continuous_re.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi

theorem isPreconnected_rightHalfPlane_v1 : IsPreconnected RightHalfPlaneV1 := by
  simpa [RightHalfPlaneV1] using (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected

private theorem seriesTerm_factor_v1 (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    seriesTerm z n =
      (z - 1) / (((n : ℂ) + 1) * (z + n)) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + (n : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  unfold seriesTerm
  rw [eq_div_iff (mul_ne_zero hn1 hzn)]
  field_simp
  ring

private theorem seriesTerm_differentiableOn_v1 (n : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => seriesTerm z n) RightHalfPlaneV1 := by
  intro z hz
  have hzn : z + (n : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [RightHalfPlaneV1] at hz
    simp at hre
    linarith
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  apply DifferentiableAt.differentiableWithinAt
  unfold seriesTerm
  fun_prop

/-- The digamma-series tsum is holomorphic at every point of the open right
half-plane.  The bound is local, so no false global uniformity claim is used. -/
private theorem differentiableAt_series_tsum_v1
    (z0 : ℂ) (hz0 : z0 ∈ RightHalfPlaneV1) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, seriesTerm z n) z0 := by
  have hz0re : 0 < z0.re := hz0
  let δ : ℝ := min (1 / 2 : ℝ) (z0.re / 4)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδle1 : δ ≤ 1 := by
    dsimp [δ]
    linarith [min_le_left (1 / 2 : ℝ) (z0.re / 4)]
  have h4δ : 4 * δ ≤ z0.re := by
    dsimp [δ]
    have h := min_le_right (1 / 2 : ℝ) (z0.re / 4)
    linarith
  let U : Set ℂ := Metric.ball z0 δ
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hz0U : z0 ∈ U := by
    simpa [U] using Metric.mem_ball_self (x := z0) hδpos

  let A : ℝ := δ + ‖z0 - 1‖
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  let majorant : ℕ → ℝ := fun n =>
    (A / δ) * (1 / (((n : ℝ) + 1) ^ 2))
  have hmajorant : Summable majorant := by
    have hp :
        Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
      have h2 :=
        (summable_nat_add_iff
          (f := fun n : ℕ => 1 / ((n : ℝ) ^ 2)) 1).2 h
      refine h2.congr fun n => ?_
      push_cast
      ring
    exact hp.mul_left (A / δ)

  have hterm :
      ∀ n : ℕ, DifferentiableOn ℂ (fun z : ℂ => seriesTerm z n) U := by
    intro n z hz
    have hzdist : ‖z - z0‖ < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm] using hz
    have hreabs : |z.re - z0.re| ≤ ‖z - z0‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z0)
    have hreldiff : |z.re - z0.re| < δ :=
      lt_of_le_of_lt hreabs hzdist
    have hzre : δ < z.re := by
      have hlow := (abs_lt.mp hreldiff).1
      nlinarith
    have hzre0 : 0 < z.re := lt_trans hδpos hzre
    have hzn : z + (n : ℂ) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    apply DifferentiableAt.differentiableWithinAt
    unfold seriesTerm
    fun_prop

  have hbound :
      ∀ n : ℕ, ∀ z ∈ U, ‖seriesTerm z n‖ ≤ majorant n := by
    intro n z hz
    have hzdist : ‖z - z0‖ < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm] using hz
    have hreabs : |z.re - z0.re| ≤ ‖z - z0‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z0)
    have hreldiff : |z.re - z0.re| < δ :=
      lt_of_le_of_lt hreabs hzdist
    have hzre : δ < z.re := by
      have hlow := (abs_lt.mp hreldiff).1
      nlinarith
    have hzre0 : 0 < z.re := lt_trans hδpos hzre
    have hnum : ‖z - 1‖ ≤ A := by
      rw [show z - 1 = (z - z0) + (z0 - 1) by ring]
      calc
        ‖(z - z0) + (z0 - 1)‖
            ≤ ‖z - z0‖ + ‖z0 - 1‖ := norm_add_le _ _
        _ ≤ δ + ‖z0 - 1‖ := by linarith
        _ = A := by rfl
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1pos : 0 < (n : ℝ) + 1 := by positivity
    have hδn :
        δ * ((n : ℝ) + 1) ≤ (n : ℝ) + z.re := by
      have hmul :
          δ * (n : ℝ) ≤ (n : ℝ) := by
        have := mul_le_mul_of_nonneg_right hδle1 hn0
        nlinarith
      nlinarith
    have hnormzn :
        (n : ℝ) + z.re ≤ ‖z + (n : ℂ)‖ := by
      have h := Complex.re_le_norm (z + (n : ℂ))
      simp [Complex.add_re] at h
      linarith
    have hdenlower :
        δ * ((n : ℝ) + 1) ≤ ‖z + (n : ℂ)‖ :=
      hδn.trans hnormzn
    have hnormn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (Complex.norm_natCast (n + 1))
    have hdenpos : 0 < ‖z + (n : ℂ)‖ := by
      have : 0 < δ * ((n : ℝ) + 1) := mul_pos hδpos hn1pos
      exact this.trans_le hdenlower
    rw [seriesTerm_factor_v1 z hzre0 n, norm_div, norm_mul, hnormn1]
    calc
      ‖z - 1‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ)‖)
          ≤ A / (((n : ℝ) + 1) *
              (δ * ((n : ℝ) + 1))) := by
            apply div_le_div₀
            · exact hA0
            · exact hnum
            · exact mul_pos hn1pos (mul_pos hδpos hn1pos)
            · exact mul_le_mul_of_nonneg_left
                hdenlower (by positivity)
      _ = (A / δ) * (1 / (((n : ℝ) + 1) ^ 2)) := by
            field_simp [hδpos.ne', hn1pos.ne']
      _ = majorant n := by rfl

  have hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => ∑' n : ℕ, seriesTerm z n) U :=
    Complex.differentiableOn_tsum_of_summable_norm
      hmajorant hterm hUopen hbound
  exact hdiff.differentiableAt (hUopen.mem_nhds hz0U)

theorem analyticOnNhd_series_tsum_v1 :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∑' n : ℕ, seriesTerm z n)
      RightHalfPlaneV1 := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (differentiableAt_series_tsum_v1 z hz).differentiableWithinAt
  · exact isOpen_rightHalfPlane_v1

theorem analyticOnNhd_digamma_add_gamma_v1 :
    AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.digamma z + (γ : ℂ))
      RightHalfPlaneV1 := by
  have hGammaDiff :
      DifferentiableOn ℂ Complex.Gamma RightHalfPlaneV1 := by
    intro z hz
    have hzre : 0 < z.re := hz
    exact
      (Complex.differentiableAt_Gamma z (by
        intro m hm
        have hre := congrArg Complex.re hm
        simp at hre
        linarith)).differentiableWithinAt
  have hGammaAnal :
      AnalyticOnNhd ℂ Complex.Gamma RightHalfPlaneV1 :=
    hGammaDiff.analyticOnNhd isOpen_rightHalfPlane_v1
  have hDigammaAnal :
      AnalyticOnNhd ℂ Complex.digamma RightHalfPlaneV1 := by
    have hfun : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
      funext z
      simp [Complex.digamma_def, logDeriv_apply]
    rw [hfun]
    exact hGammaAnal.deriv.div hGammaAnal
      (fun z hz => Complex.Gamma_ne_zero_of_re_pos hz)
  exact hDigammaAnal.add analyticOnNhd_const

private theorem one_mem_closure_real_axis_equalities_v1 :
    (1 : ℂ) ∈ closure
      ({z : ℂ |
          Complex.digamma z + (γ : ℂ) =
            ∑' n : ℕ, seriesTerm z n} \ {(1 : ℂ)}) := by
  let s : ℕ → ℂ := fun n =>
    (1 : ℂ) + 1 / ((n + 1 : ℕ) : ℂ)
  have hs_tend : Tendsto s atTop (𝓝 (1 : ℂ)) := by
    have hzero :
        Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ))
          atTop (𝓝 0) :=
      by simpa [Nat.cast_add, Nat.cast_one] using
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
    simpa [s] using (tendsto_const_nhds.add hzero)
  refine mem_closure_of_tendsto hs_tend ?_
  exact Filter.Eventually.of_forall (fun n => by
    constructor
    · let x : ℝ := 1 + 1 / ((n + 1 : ℕ) : ℝ)
      have hx : 0 < x := by
        dsimp [x]
        positivity
      have hreal := digamma_series_ofReal_v1 x hx
      simpa [s, x] using hreal
    · simpa [s] using (Nat.cast_add_one_ne_zero n : ((n : ℂ) + 1) ≠ 0))

/-- The missing series representation of the complex digamma function on the
entire open right half-plane. -/
theorem digamma_series_halfPlane_v1 (z : ℂ) (hz : 0 < z.re) :
    Complex.digamma z + (γ : ℂ) =
      ∑' n : ℕ, seriesTerm z n := by
  let F : ℂ → ℂ := fun w => Complex.digamma w + (γ : ℂ)
  let G : ℂ → ℂ := fun w => ∑' n : ℕ, seriesTerm w n
  have hEq : EqOn F G RightHalfPlaneV1 := by
    refine
      analyticOnNhd_digamma_add_gamma_v1.eqOn_of_preconnected_of_mem_closure
        analyticOnNhd_series_tsum_v1
        isPreconnected_rightHalfPlane_v1
        (z₀ := (1 : ℂ))
        (by simp [RightHalfPlaneV1])
        ?_
    simpa [F, G] using one_mem_closure_real_axis_equalities_v1
  exact hEq hz

/-- Full Gauss integral representation, now derived from the pinned Mathlib
trust surface plus the existing AEGIS series-to-integral theorem. -/
theorem gauss_digamma_integral_v1 (z : ℂ) (hz : 0 < z.re) :
    Complex.digamma z + (γ : ℂ) =
      ∫ u in Ioi (0 : ℝ), gaussIntegrand z u := by
  rw [digamma_series_halfPlane_v1 z hz]
  exact tsum_seriesTerm_eq_integral z hz

end AEGIS.WeilDigammaSeriesHalfPlaneV1

#print axioms AEGIS.WeilDigammaSeriesHalfPlaneV1.analyticOnNhd_series_tsum_v1
#print axioms AEGIS.WeilDigammaSeriesHalfPlaneV1.analyticOnNhd_digamma_add_gamma_v1
#print axioms AEGIS.WeilDigammaSeriesHalfPlaneV1.digamma_series_halfPlane_v1
#print axioms AEGIS.WeilDigammaSeriesHalfPlaneV1.gauss_digamma_integral_v1
