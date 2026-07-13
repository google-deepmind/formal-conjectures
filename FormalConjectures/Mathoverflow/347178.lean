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

import FormalConjectures.Util.ProblemImports

/-!
# Mathoverflow 347178

*Reference:* [mathoverflow/347178](https://mathoverflow.net/questions/347178)
asked by user [*Biagio Ricceri*](https://mathoverflow.net/users/149235/biagio-ricceri)

The original question has a negative answer, witnessed by the logarithmic-spiral counterexample
formalized below in $\mathbb R^2$.
-/
open Real Set Filter
open scoped EuclideanGeometry Topology
namespace Mathoverflow347178

noncomputable section

/-- The standard identification of Lean's `ℝ²` with the complex plane. -/
abbrev planeToComplex : ℝ² ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/--
The counterexample on the complex plane. In polar coordinates $z = r e^{i\theta}$ this is
$r^2(e^\pi\cos(\theta-\log r)-1/2)$, with value $0$ at the origin.
-/
noncomputable def spiralCounterexampleAux (z : ℂ) : ℝ :=
  ‖z‖ ^ 2 * (Real.exp Real.pi * Real.cos (Complex.arg z - Real.log ‖z‖) - 1 / 2)

/--
The logarithmic-spiral counterexample as a function on $\mathbb R^2$.
-/
noncomputable def spiralCounterexample (x : ℝ²) : ℝ :=
  spiralCounterexampleAux (planeToComplex x)

/-- Points on the positive real axis with radius $e^{2\pi n}$. -/
noncomputable def spiralPoint (n : ℕ) : ℝ² :=
  planeToComplex.symm ((Real.exp (n * (2 * Real.pi)) : ℝ) : ℂ)

/--
On the positive-axis subsequence $r = e^{2\pi n}$, the counterexample has value
$r^2(e^\pi - 1/2)$.
-/
@[category API, AMS 26]
theorem spiralCounterexample_spiralPoint (n : ℕ) :
    spiralCounterexample (spiralPoint n) =
      (Real.exp (n * (2 * Real.pi))) ^ 2 * (Real.exp Real.pi - 1 / 2) := by
  unfold spiralPoint spiralCounterexample spiralCounterexampleAux planeToComplex
  rw [LinearIsometryEquiv.apply_symm_apply]
  rw [Complex.arg_ofReal_of_nonneg (Real.exp_pos _).le]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [Real.log_exp]
  have hcos : Real.cos (0 - n * (2 * Real.pi)) = 1 := by
    rw [zero_sub, Real.cos_neg]
    exact Real.cos_nat_mul_two_pi n
  rw [hcos]
  ring

open scoped Gradient

/-
### Complex-plane analysis

We transport the counterexample to the complex plane through `planeToComplex` and do the
calculus there.
-/

/--
The `arg`-free oscillating part of `spiralCounterexampleAux`. It equals
`‖z‖ ^ 2 * cos (arg z - log ‖z‖)`, but is expressed using complex exponentials.
-/
noncomputable def spiralHeight (z : ℂ) : ℝ :=
  (starRingEnd ℂ z * Complex.exp ((1 + Complex.I) * (Real.log ‖z‖ : ℂ))).re

@[category API, AMS 26]
private lemma spiralCounterexampleAux_eq_height (z : ℂ) :
    spiralCounterexampleAux z = Real.exp Real.pi * spiralHeight z - ‖z‖ ^ 2 / 2 := by
  by_cases hz : z = 0
  · unfold spiralCounterexampleAux spiralHeight
    norm_num [hz]
  · unfold spiralCounterexampleAux spiralHeight
    norm_num [Complex.exp_re, Complex.exp_im, Real.cos_sub]
    rw [Real.exp_log (norm_pos_iff.mpr hz)]
    rw [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg]
    ring

/-- The gradient of `spiralHeight` away from the origin, represented as a complex number. -/
noncomputable def gradSpiralHeight (z : ℂ) : ℂ :=
  (3 + Complex.I) / 2 * Complex.exp ((1 + Complex.I) * (Real.log ‖z‖ : ℂ)) +
    (1 - Complex.I) / 2 * z ^ 2 *
      Complex.exp ((-1 - Complex.I) * (Real.log ‖z‖ : ℂ))

/-- The image of `z` under `z ↦ z + ∇ spiralCounterexampleAux z` on the complex plane. -/
noncomputable def newPoint (z : ℂ) : ℂ :=
  if z = 0 then 0 else (Real.exp Real.pi : ℂ) * gradSpiralHeight z

/-- The gradient of `spiralCounterexampleAux`, represented as a complex number. -/
noncomputable def spiralGradient (z : ℂ) : ℂ :=
  newPoint z - z

@[category API, AMS 26]
private lemma hasGradientAt_spiralHeight_of_ne {z : ℂ} (hz : z ≠ 0) :
    HasGradientAt spiralHeight (gradSpiralHeight z) z := by
  unfold spiralHeight gradSpiralHeight
  have hz' : 0 < z.re ^ 2 + z.im ^ 2 := by
    contrapose! hz
    apply Complex.ext
    · rw [Complex.zero_re]; nlinarith
    · rw [Complex.zero_im]; nlinarith
  simp [Complex.exp_re, Complex.exp_im, mul_comm]
  apply (HasFDerivAt.congr_of_eventuallyEq
    (f := fun z : ℂ =>
      z.re * (‖z‖ * Real.cos (Real.log ‖z‖)) +
        z.im * (‖z‖ * Real.sin (Real.log ‖z‖))))
  · apply (HasFDerivAt.congr_of_eventuallyEq
      (f := fun z : ℂ =>
        z.re *
            (Real.sqrt (z.re ^ 2 + z.im ^ 2) *
              Real.cos (Real.log (Real.sqrt (z.re ^ 2 + z.im ^ 2)))) +
          z.im *
            (Real.sqrt (z.re ^ 2 + z.im ^ 2) *
              Real.sin (Real.log (Real.sqrt (z.re ^ 2 + z.im ^ 2))))))
    · convert HasFDerivAt.add
          (HasFDerivAt.mul Complex.reCLM.hasFDerivAt
            (HasFDerivAt.mul
              (HasFDerivAt.sqrt
                (HasFDerivAt.add (Complex.reCLM.hasFDerivAt.pow 2)
                  (Complex.imCLM.hasFDerivAt.pow 2)) _)
              (HasFDerivAt.cos
                (HasFDerivAt.log
                  (HasFDerivAt.sqrt
                    (HasFDerivAt.add (Complex.reCLM.hasFDerivAt.pow 2)
                      (Complex.imCLM.hasFDerivAt.pow 2)) _) _))))
          (HasFDerivAt.mul Complex.imCLM.hasFDerivAt
            (HasFDerivAt.mul
              (HasFDerivAt.sqrt
                (HasFDerivAt.add (Complex.reCLM.hasFDerivAt.pow 2)
                  (Complex.imCLM.hasFDerivAt.pow 2)) _)
              (HasFDerivAt.sin
                (HasFDerivAt.log
                  (HasFDerivAt.sqrt
                    (HasFDerivAt.add (Complex.reCLM.hasFDerivAt.pow 2)
                      (Complex.imCLM.hasFDerivAt.pow 2)) _) _)))) using 1
      all_goals norm_num [Complex.ext_iff, sq]
      any_goals
        rw [Real.sqrt_eq_zero']
        contrapose! hz
        simp_all [Complex.ext_iff]
      any_goals nlinarith [Complex.normSq_apply z, Complex.sq_norm z,
        show 0 < Complex.normSq z from Complex.normSq_pos.mpr hz]
      · ext
        norm_num [Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im,
          Complex.normSq, Complex.norm_def]
        ring_nf
        norm_num [Complex.normSq, Complex.norm_def, Real.exp_neg,
          Real.exp_log (Real.sqrt_pos.mpr (hz'))]
        ring_nf
        grind
      · nlinarith
      · nlinarith
    · filter_upwards [IsOpen.mem_nhds isOpen_ne hz] with x hx using by
        simp [Complex.normSq, Complex.norm_def, sq]
  · filter_upwards [IsOpen.mem_nhds isOpen_ne hz] with x hx using by
      rw [Real.exp_log (norm_pos_iff.mpr hx)]
      ring_nf

@[category API, AMS 26]
private lemma hasGradientAt_spiralHeight_zero : HasGradientAt spiralHeight 0 0 := by
  have h_bound : ∀ z : ℂ, |spiralHeight z| ≤ ‖z‖ ^ 2 := by
    intro z
    by_cases hz : z = 0
    · unfold spiralHeight
      aesop
    · convert Complex.abs_re_le_norm
          (starRingEnd ℂ z *
            Complex.exp ((1 + Complex.I) * (Real.log ‖z‖ : ℂ))) using 1
      norm_num [Complex.exp_re, Complex.exp_im, Real.exp_log (norm_pos_iff.mpr hz)]
      ring_nf
      norm_num [Complex.norm_exp, sq]
      exact Or.inl (by rw [Real.exp_log (norm_pos_iff.mpr hz)])
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.isLittleO_iff.2
  intro ε ε_pos
  filter_upwards [Metric.ball_mem_nhds _ ε_pos] with x hx
  specialize h_bound x
  simp_all [sq]
  have h_zero : spiralHeight 0 = 0 := by
    unfold spiralHeight
    norm_num
  rw [h_zero]
  simpa using h_bound.trans (mul_le_mul_of_nonneg_right hx.le (norm_nonneg x))

@[category API, AMS 26]
private lemma hasGradientAt_norm_sq_div_two (z : ℂ) :
    HasGradientAt (fun w : ℂ => ‖w‖ ^ 2 / 2) z z := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  norm_num [Asymptotics.isLittleO_iff, Complex.normSq, Complex.sq_norm]
  intro ε ε_pos
  filter_upwards [Metric.ball_mem_nhds _ ε_pos] with x hx
  rw [Complex.norm_def]
  simp_all [Complex.normSq, Complex.norm_def]
  rw [abs_le]
  constructor
  any_goals nlinarith [sq_nonneg (x.re - x.im), sq_nonneg (x.re + x.im),
      Real.sqrt_nonneg (x.re * x.re + x.im * x.im),
      Real.mul_self_sqrt (add_nonneg (mul_self_nonneg x.re) (mul_self_nonneg x.im))]

@[category API, AMS 26]
private lemma hasGradientAt_spiralCounterexampleAux (z : ℂ) :
    HasGradientAt spiralCounterexampleAux (spiralGradient z) z := by
  by_cases hz : z = 0
  · simp [hz, spiralGradient]
    unfold newPoint
    rw [show spiralCounterexampleAux =
        fun w => Real.exp Real.pi * spiralHeight w - ‖w‖ ^ 2 / 2 by
      ext
      exact spiralCounterexampleAux_eq_height _]
    rw [hasGradientAt_iff_hasFDerivAt] at *
    convert HasFDerivAt.sub
        (HasFDerivAt.const_mul hasGradientAt_spiralHeight_zero.hasFDerivAt (Real.exp Real.pi))
        (hasGradientAt_norm_sq_div_two 0).hasFDerivAt using 1
    norm_num
  · rw [show spiralCounterexampleAux = _ from funext fun w => spiralCounterexampleAux_eq_height w]
    simp [spiralGradient, newPoint]
    have hheight := hasGradientAt_spiralHeight_of_ne hz
    rw [hasGradientAt_iff_hasFDerivAt] at *
    convert HasFDerivAt.sub
        (hheight.const_smul (Real.exp Real.pi))
        (hasGradientAt_norm_sq_div_two z).hasFDerivAt using 1
    norm_num [hz]
    ring_nf
    ext
    simp [Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    ring

@[category API, AMS 26]
private lemma continuous_spiralGradient : Continuous spiralGradient := by
  have h_newPoint_cont : ContinuousAt newPoint 0 := by
    have h_lim : ∀ z : ℂ, z ≠ 0 →
        ‖newPoint z‖ ≤ Real.exp Real.pi *
          (‖(3 + Complex.I) / 2‖ + ‖(1 - Complex.I) / 2‖) * ‖z‖ := by
      intro z hz
      have h_grad :
          ‖gradSpiralHeight z‖ ≤
            ‖(3 + Complex.I) / 2‖ * ‖z‖ + ‖(1 - Complex.I) / 2‖ * ‖z‖ := by
        apply le_trans (norm_add_le _ _)
        · norm_num [Complex.norm_exp]
          norm_num [Real.exp_neg, Real.exp_log (norm_pos_iff.mpr hz)]
          norm_num [sq, mul_assoc, hz]
      convert mul_le_mul_of_nonneg_left h_grad (Real.exp_nonneg Real.pi) using 1
      all_goals ring_nf
      unfold newPoint
      aesop
    have h_squeeze :
        Filter.Tendsto
          (fun z : ℂ =>
            Real.exp Real.pi * (‖(3 + Complex.I) / 2‖ + ‖(1 - Complex.I) / 2‖) * ‖z‖)
          (𝓝 0) (𝓝 0) := by
      exact Continuous.tendsto' (by continuity) 0 0 (by simp)
    exact continuousAt_of_tendsto_nhds
      (squeeze_zero_norm (fun z => if h : z = 0 then by
        simp [h, newPoint]
      else h_lim z h) h_squeeze)
  have h_newPoint_cont_ne_zero : ∀ z : ℂ, z ≠ 0 → ContinuousAt newPoint z := by
    intro z hz
    have h_grad_cont : ContinuousAt (fun z : ℂ => gradSpiralHeight z) z := by
      have hlog_cont : ContinuousAt (fun x : ℂ => (Real.log ‖x‖ : ℂ)) z :=
        Complex.continuous_ofReal.continuousAt.comp
          (ContinuousAt.log continuousAt_id.norm (by simpa))
      apply ContinuousAt.add
      · exact ContinuousAt.mul continuousAt_const
          (Complex.continuous_exp.continuousAt.comp
            (ContinuousAt.mul continuousAt_const hlog_cont))
      · exact ContinuousAt.mul
          (ContinuousAt.mul continuousAt_const (continuousAt_id.pow 2))
          (Complex.continuous_exp.continuousAt.comp
            (ContinuousAt.mul continuousAt_const hlog_cont))
    exact ContinuousAt.congr (ContinuousAt.mul continuousAt_const h_grad_cont)
      (Filter.EventuallyEq.symm
        (Filter.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hz) fun x hx =>
          if_neg hx))
  exact Continuous.sub
    (continuous_iff_continuousAt.mpr fun z =>
      if h : z = 0 then h.symm ▸ h_newPoint_cont else h_newPoint_cont_ne_zero z h)
    continuous_id

@[category API, AMS 26]
private lemma contDiff_spiralCounterexampleAux :
    ContDiff ℝ 1 spiralCounterexampleAux := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · exact fun x => (hasGradientAt_spiralCounterexampleAux x).differentiableAt
  · convert (InnerProductSpace.toDual ℝ ℂ).continuous.comp continuous_spiralGradient using 1
    ext z
    have h_fderiv :=
      congr_arg (fun f => f ‹_›)
        (hasGradientAt_spiralCounterexampleAux z).hasFDerivAt.fderiv
    convert h_fderiv using 1

@[category API, AMS 26]
private lemma spiralHeight_eq (w : ℂ) :
    spiralHeight w = ‖w‖ ^ 2 * Real.cos (Complex.arg w - Real.log ‖w‖) := by
  unfold spiralHeight
  by_cases hw : w = 0
  all_goals simp_all [Complex.exp_re, Complex.exp_im, Real.cos_sub]
  rw [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg]
  ring_nf
  rw [Real.exp_log (norm_pos_iff.mpr hw)]
  ring_nf

@[category API, AMS 26]
private lemma spiralHeight_exp_mul (r : ℝ) (w : ℂ) :
    spiralHeight (Complex.exp ((1 + Complex.I) * (r : ℂ)) * w) =
      Real.exp (2 * r) * spiralHeight w := by
  by_cases hw : w = 0
  all_goals simp_all [spiralHeight]
  norm_num [Complex.exp_re, Complex.exp_im, Complex.norm_exp]
  ring_nf
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.exp_add, Real.exp_mul, Real.exp_log (by positivity)]
  norm_num
  rw [Real.sin_add, Real.cos_add]
  ring_nf
  rw [Real.sin_sq, Real.cos_sq]
  ring_nf

@[category API, AMS 26]
private lemma spiralHeight_exp_pi_mul (w : ℂ) :
    spiralHeight ((Real.exp Real.pi : ℂ) * w) =
      -(Real.exp (2 * Real.pi)) * spiralHeight w := by
  rw [spiralHeight_eq, spiralHeight_eq]
  by_cases hw : w = 0
  all_goals simp_all
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  ring_nf
  rw [show (Complex.exp π * w).arg = w.arg by
        convert Complex.arg_real_mul w (Real.exp_pos Real.pi) using 1
        norm_num [Complex.exp_ofReal_re]]
  norm_num [Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub, Real.exp_mul]
  ring

/-- The unit-circle model of the new point, after factoring out the on-spiral dilation. -/
noncomputable def spiralUnit (u : ℂ) : ℂ :=
  (3 + Complex.I) / 2 + (1 - Complex.I) / 2 * u

@[category API, AMS 26]
private lemma gradSpiralHeight_factor (z : ℂ) :
    gradSpiralHeight z =
      Complex.exp ((1 + Complex.I) * (Real.log ‖z‖ : ℂ)) *
        spiralUnit (z ^ 2 * Complex.exp ((-2 - 2 * Complex.I) * (Real.log ‖z‖ : ℂ))) := by
  unfold gradSpiralHeight spiralUnit
  ring_nf
  norm_num [mul_assoc, mul_comm, mul_left_comm, ← Complex.exp_add]
  ring_nf

@[category API, AMS 26]
private lemma unitFactor_norm {z : ℂ} (hz : z ≠ 0) :
    ‖z ^ 2 * Complex.exp ((-2 - 2 * Complex.I) * (Real.log ‖z‖ : ℂ))‖ = 1 := by
  have hz' : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have hre :
      ((-2 - 2 * Complex.I) * (Real.log ‖z‖ : ℂ)).re =
        -(Real.log ‖z‖ + Real.log ‖z‖) := by
    simp [Complex.mul_re]
    ring
  rw [hre, Real.exp_neg, Real.exp_add, Real.exp_log hz']
  field_simp [sq]

@[category API, AMS 26]
private lemma spiralUnit_re_nonneg {u : ℂ} (hu : ‖u‖ = 1) :
    0 ≤ (spiralUnit u).re := by
  unfold spiralUnit
  norm_num [Complex.ext_iff]
  nlinarith [sq_nonneg (u.re - u.im), sq_nonneg (u.re + u.im),
    Complex.normSq_apply u, Complex.sq_norm u]

@[category API, AMS 26]
private lemma spiralHeight_spiralUnit_nonneg {u : ℂ} (hu : ‖u‖ = 1) :
    0 ≤ spiralHeight (spiralUnit u) := by
  have h_height :
      spiralHeight (spiralUnit u) =
        ‖spiralUnit u‖ ^ 2 *
          Real.cos (Complex.arg (spiralUnit u) - Real.log ‖spiralUnit u‖) := by
    convert spiralHeight_eq (spiralUnit u) using 1
  have h_arg_bounds :
      -(Real.pi / 6) ≤ Complex.arg (spiralUnit u) ∧
        Complex.arg (spiralUnit u) ≤ Real.pi / 4 := by
    constructor
    · by_cases h_im_neg : (spiralUnit u).im < 0
      · have h_t_ge_neg_half : (spiralUnit u).im / ‖spiralUnit u‖ ≥ -1 / 2 := by
          rw [ge_iff_le, div_le_div_iff₀]
          all_goals norm_num [Complex.normSq, Complex.norm_def] at *
          · unfold spiralUnit at *
            norm_num at *
            rw [neg_le]
            exact Real.le_sqrt_of_sq_le
              (by nlinarith [sq_nonneg (u.re - u.im), sq_nonneg (u.re + u.im)])
          · nlinarith
        have h_arg :
            Complex.arg (spiralUnit u) =
              Real.arcsin ((spiralUnit u).im / ‖spiralUnit u‖) := by
          rw [Complex.arg, Complex.norm_def]
          rw [if_pos]
          exact spiralUnit_re_nonneg hu
        rw [h_arg, Real.le_arcsin_iff_sin_le']
        · norm_num
          linarith
        · constructor
          · linarith [Real.pi_pos]
          · linarith [Real.pi_pos]
      · linarith [Real.pi_pos, Complex.arg_nonneg_iff.mpr (le_of_not_gt h_im_neg)]
    · have h_arg :
          Complex.arg (spiralUnit u) =
            Real.arcsin ((spiralUnit u).im / ‖spiralUnit u‖) :=
        Complex.arg_of_re_nonneg (spiralUnit_re_nonneg hu)
      rw [h_arg, Real.arcsin_le_iff_le_sin]
      · norm_num [Complex.normSq, Complex.norm_def] at *
        rw [div_le_div_iff₀]
        all_goals norm_num [spiralUnit]
        · rw [← Real.sqrt_mul (by positivity)]
          exact Real.le_sqrt_of_sq_le
            (by nlinarith [sq_nonneg (u.re - u.im), sq_nonneg (u.re + u.im)])
        · nlinarith [sq_nonneg (u.re - u.im)]
      · constructor
        · rw [le_div_iff₀
            (norm_pos_iff.mpr (show spiralUnit u ≠ 0 from by
              unfold spiralUnit
              norm_num [Complex.ext_iff]
              intro h
              nlinarith [Complex.normSq_apply u, Complex.sq_norm u]))]
          linarith [abs_le.mp (Complex.abs_im_le_norm (spiralUnit u))]
        · rw [div_le_one₀
            (norm_pos_iff.mpr (show spiralUnit u ≠ 0 from by
              unfold spiralUnit
              norm_num [Complex.ext_iff]
              intro h
              nlinarith [Complex.normSq_apply u, Complex.sq_norm u]))]
          linarith [abs_le.mp (Complex.abs_im_le_norm (spiralUnit u))]
      · constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
  have h_log_bounds :
      -(Real.pi / 4) ≤ Real.log ‖spiralUnit u‖ ∧
        Real.log ‖spiralUnit u‖ ≤ Real.pi / 3 := by
    have h_norm_sq_bounds :
        3 - Real.sqrt 5 ≤ ‖spiralUnit u‖ ^ 2 ∧
          ‖spiralUnit u‖ ^ 2 ≤ 3 + Real.sqrt 5 := by
      norm_num [Complex.normSq, Complex.norm_def, spiralUnit] at *
      rw [Real.sq_sqrt (by nlinarith)]
      ring_nf
      norm_num
      constructor
      · nlinarith only [sq_nonneg (u.re * 2 - u.im), sq_nonneg (u.re * 2 + u.im),
          hu, Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
      · nlinarith only [sq_nonneg (u.re * 2 - u.im), sq_nonneg (u.re * 2 + u.im),
          hu, Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    constructor
    · have h_log_bound_left : Real.log (3 - Real.sqrt 5) ≥ -Real.pi / 2 := by
        have hlog : Real.log (Real.exp (-1)) ≤ Real.log (3 - Real.sqrt 5) :=
          Real.log_le_log (by positivity) (by
            have := Real.exp_neg_one_lt_d9
            norm_num1 at *
            nlinarith [Real.sqrt_nonneg 5,
              Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)])
        have hpi : -Real.pi / 2 ≤ Real.log (Real.exp (-1)) := by
          norm_num
          linarith [Real.pi_gt_three]
        exact le_trans hpi hlog
      have hlog_norm : Real.log (‖spiralUnit u‖ ^ 2) ≥ -Real.pi / 2 :=
        h_log_bound_left.trans
          (Real.log_le_log
            (by nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)])
            h_norm_sq_bounds.1)
      rw [Real.log_pow] at hlog_norm
      norm_num at hlog_norm
      linarith
    · have h_log_upper : Real.log (3 + Real.sqrt 5) ≤ 2 * Real.pi / 3 := by
        rw [Real.log_le_iff_le_exp (by positivity)]
        have h_exp_gt : Real.exp (2 * Real.pi / 3) > 5.24 := by
          have hgt : Real.exp (2 * Real.pi / 3) > Real.exp 2 :=
            Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
          exact lt_of_le_of_lt (by
            have := Real.exp_one_gt_d9.le
            norm_num1 at *
            rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
            nlinarith [Real.add_one_le_exp 1]) hgt
        norm_num at h_exp_gt
        nlinarith only [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num),
          h_exp_gt]
      have hlog_norm :=
        Real.log_le_log
          (by nlinarith [Real.sqrt_nonneg 5,
            Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), norm_nonneg (spiralUnit u)])
          h_norm_sq_bounds.2
      rw [Real.log_pow] at hlog_norm
      norm_num at hlog_norm
      linarith
  exact h_height.symm ▸
    mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)

@[category API, AMS 26]
private lemma spiralHeight_gradSpiralHeight_nonneg {z : ℂ} (hz : z ≠ 0) :
    0 ≤ spiralHeight (gradSpiralHeight z) := by
  rw [gradSpiralHeight_factor, spiralHeight_exp_mul]
  have h2 := spiralHeight_spiralUnit_nonneg (unitFactor_norm hz)
  positivity

@[category API, AMS 26]
private lemma spiralCounterexampleAux_newPoint_nonpos (z : ℂ) :
    spiralCounterexampleAux (newPoint z) ≤ 0 := by
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz, newPoint, spiralCounterexampleAux]
  · have hnp : newPoint z = (Real.exp Real.pi : ℂ) * gradSpiralHeight z := by
      simp [newPoint, hz]
    rw [spiralCounterexampleAux_eq_height, hnp, spiralHeight_exp_pi_mul]
    have hpos : 0 ≤ Real.exp (2 * Real.pi) * spiralHeight (gradSpiralHeight z) :=
      mul_nonneg (Real.exp_pos _).le (spiralHeight_gradSpiralHeight_nonneg hz)
    have hsq : 0 ≤ ‖(Real.exp Real.pi : ℂ) * gradSpiralHeight z‖ ^ 2 / 2 := by positivity
    nlinarith [Real.exp_pos Real.pi]

@[category API, AMS 26]
private lemma gradient_comp_linearIsometryEquiv
    {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
    (e : E ≃ₗᵢ[ℝ] E') (f : E' → ℝ) (x : E) :
    gradient (f ∘ e) x = e.symm (gradient f (e x)) := by
  by_cases h : DifferentiableAt ℝ f (e x)
  · simp only [gradient]
    rw [fderiv_comp]
    all_goals norm_num [h, e.differentiableAt]
    rw [show fderiv ℝ (e : E → E') x = e.toContinuousLinearEquiv.toContinuousLinearMap from ?_]
    · apply (InnerProductSpace.toDual ℝ E).injective
      ext y
      simp
      rw [← e.inner_map_map]
      simp
    · exact HasFDerivAt.fderiv e.toContinuousLinearEquiv.hasFDerivAt
  · by_cases h' : DifferentiableAt ℝ (f ∘ e) x
    · simp_all [gradient]
      contrapose! h
      have hf_eq : f = (f ∘ e) ∘ e.symm := by
        ext
        simp
      rw [hf_eq]
      exact DifferentiableAt.comp _ (by simpa) e.symm.differentiableAt
    · simp_all [gradient]
      rw [fderiv_zero_of_not_differentiableAt h', fderiv_zero_of_not_differentiableAt h]
      simp

/-
### Counterexample properties

The next theorems expose the counterexample: it is \(C^1\), unbounded above, but becomes
nonpositive after the map \(x \mapsto x+\nabla f(x)\).
-/

/--
The logarithmic-spiral counterexample is $C^1$ on $\mathbb R^2$.

Away from the origin this follows from the polar-coordinate formula. At the origin, the function is
$O(r^2)$ and its gradient is $O(r)$.
-/
@[category API, AMS 26]
theorem spiralCounterexample_contDiff :
    ContDiff ℝ 1 spiralCounterexample := by
  change ContDiff ℝ 1 (spiralCounterexampleAux ∘ planeToComplex)
  exact contDiff_spiralCounterexampleAux.comp planeToComplex.contDiff

/--
The counterexample is unbounded above. Along the logarithmic spiral $\theta = \log r$, it is
$r^2(e^\pi-1/2)$, which tends to $+\infty$.
-/
@[category API, AMS 26]
theorem spiralCounterexample_not_bddAbove :
    ¬ BddAbove (range spiralCounterexample) := by
  have hc : 0 < Real.exp Real.pi - (1 / 2 : ℝ) := by
    nlinarith [Real.exp_pos Real.pi, Real.one_lt_exp_iff.mpr Real.pi_pos]
  have hlin :
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * (2 * Real.pi)) Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.atTop_mul_const (by positivity) tendsto_natCast_atTop_atTop
  have hexp :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.exp ((n : ℝ) * (2 * Real.pi))) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hsquare :
      Filter.Tendsto
        (fun n : ℕ ↦
          Real.exp ((n : ℝ) * (2 * Real.pi)) * Real.exp ((n : ℝ) * (2 * Real.pi)))
        Filter.atTop Filter.atTop :=
    hexp.atTop_mul_atTop₀ hexp
  have htendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ (Real.exp (n * (2 * Real.pi))) ^ 2 * (Real.exp Real.pi - 1 / 2))
        Filter.atTop Filter.atTop := by
    convert Filter.Tendsto.atTop_mul_const hc hsquare using 1
    ext n
    ring
  have hseq :
      Filter.Tendsto
        (fun n : ℕ ↦ spiralCounterexample (spiralPoint n)) Filter.atTop Filter.atTop := by
    simpa [spiralCounterexample_spiralPoint] using htendsto
  intro h
  exact Filter.not_bddAbove_of_tendsto_atTop hseq
    (BddAbove.mono (by
      rintro _ ⟨n, rfl⟩
      exact ⟨spiralPoint n, rfl⟩) h)

/--
After the map $x \mapsto x + \nabla f(x)$, the logarithmic-spiral counterexample is nonpositive.
This is the polar-coordinate computation: if
$R(\phi)=\sqrt{(2\cos\phi+\sin\phi)^2+\sin^2\phi}$ and $\beta(\phi)$ is the argument of
$(2\cos\phi+\sin\phi)-i\sin\phi$, then the new phase
$\phi+\beta(\phi)-\log R(\phi)-\pi$ has negative cosine.
-/
@[category API, AMS 26]
theorem spiralCounterexample_add_gradient_nonpos (x : ℝ²) :
    spiralCounterexample (x + gradient spiralCounterexample x) ≤ 0 := by
  rw [show gradient spiralCounterexample x =
      planeToComplex.symm (spiralGradient (planeToComplex x)) by
    have h : spiralCounterexample = spiralCounterexampleAux ∘ planeToComplex := rfl
    rw [h, gradient_comp_linearIsometryEquiv, gradient_eq hasGradientAt_spiralCounterexampleAux]]
  have hz :
      planeToComplex x + spiralGradient (planeToComplex x) = newPoint (planeToComplex x) := by
    simp only [spiralGradient]
    ring
  have hstep :
      x + planeToComplex.symm (spiralGradient (planeToComplex x)) =
        planeToComplex.symm (newPoint (planeToComplex x)) := by
    rw [← hz, map_add, LinearIsometryEquiv.symm_apply_apply]
  rw [hstep]
  unfold spiralCounterexample
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact spiralCounterexampleAux_newPoint_nonpos _

/--
Consequently, the values of the counterexample after $x \mapsto x + \nabla f(x)$ are bounded above
by $0$.
-/
@[category API, AMS 26]
theorem spiralCounterexample_add_gradient_bddAbove :
    BddAbove
      (range fun x : ℝ² ↦ spiralCounterexample (x + gradient spiralCounterexample x)) := by
  use 0
  rintro _ ⟨x, rfl⟩
  exact spiralCounterexample_add_gradient_nonpos x

/--
Let $f : \mathbb R^n \to \mathbb R,  n \geq 2$ be a $C^1$ function. Is it true that
$$\sup_{x \in \mathbb R^n}f(x) = \sup_{x\in \mathbb R^n} f(x+\nabla f(x))$$?

Answer: No. There is a counterexample in $\mathbb R^2$ for which $f$ is unbounded above, while
$f(x + \nabla f(x)) \leq 0$ for all $x$.
-/
@[category research solved, AMS 26]
theorem mathoverflow_347178 :
    answer(False) ↔ ∀ᵉ (n ≥ 2) (f : ℝ^n → ℝ) (_ : ContDiff ℝ 1 f),
        (BddAbove (range f) ↔ BddAbove (range (fun x ↦ f (x + gradient f x)))) ∧
        (⨆ x, (f x : EReal)) = ⨆ x, (f (x + gradient f x) : EReal) := by
  constructor
  · intro h
    cases h
  · intro h
    have h₂ := h 2 (by norm_num) spiralCounterexample spiralCounterexample_contDiff
    exact spiralCounterexample_not_bddAbove
      (h₂.1.mpr spiralCounterexample_add_gradient_bddAbove)

/--
Let $f : \mathbb R^n \to \mathbb R,  n \geq 2$ be a $C^1$ function. Is the boundedness of
$\sup_{x \in \mathbb R^n}f(x)$ and $\sup_{x\in \mathbb R^n} f(x+\nabla f(x))$ equivalent?

Answer: No. The same counterexample has $\sup f = +\infty$ but
$\sup_x f(x + \nabla f(x)) = 0$.
-/
@[category research solved, AMS 26]
theorem mathoverflow_347178.variants.bounded_iff :
    answer(False) ↔ ∀ᵉ (n ≥ 2) (f : ℝ^n → ℝ) (_ : ContDiff ℝ 1 f),
        BddAbove (range f) ↔ BddAbove (range fun x ↦ f (x + gradient f x)) := by
  constructor
  · intro h
    cases h
  · intro h
    have h₂ := h 2 (by norm_num) spiralCounterexample spiralCounterexample_contDiff
    exact spiralCounterexample_not_bddAbove
      (h₂.mpr spiralCounterexample_add_gradient_bddAbove)

/--
Let $f : \mathbb R^n \to \mathbb R,  n \geq 2$ be a $C^1$ function. Does the equality
$$\sup_{x \in \mathbb R^n}f(x) = \sup_{x\in \mathbb R^n} f(x+\nabla f(x))$$
hold when both suprema are finite?
-/
@[category research open, AMS 26]
theorem mathoverflow_347178.variants.bounded_only :
    answer(sorry) ↔ ∀ᵉ (n ≥ 2) (f : ℝ^n → ℝ) (hf : ContDiff ℝ 1 f)
        (h : BddAbove (range f)) (h' : BddAbove (range (fun x ↦ f (x + gradient f x)))),
        (⨆ x, f x) = ⨆ x, f (x + gradient f x) := by
  sorry

end

end Mathoverflow347178
