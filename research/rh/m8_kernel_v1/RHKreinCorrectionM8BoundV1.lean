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

import AEGISOverlay.RHKreinCorrectionSymbolV1
import AEGISOverlay.RHKreinM8CertificateV1
import AEGISOverlay.RHKreinSplineL1NormV1
import AEGISOverlay.RHKreinSplineDerivativesV1
import AEGISOverlay.RHKreinFourierTaylorBoundV1

/-!
# The analytic M8 bound for the exact order-19 correction symbol

Every row is a genuine compactly supported function. We differentiate its
angular Fourier transform, bound the eighth moment, and sum the exact
coefficient budgets. The one-sided rows represent the real correction symbol;
they are not asserted to equal the Hermitian time-domain correction.

No pointwise positivity, cell soundness or RH is assumed or concluded.
AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex FourierTransform
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinCorrectionM8BoundV1

open AEGIS.RHKreinExplicitCorrectionV1 AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinSplineSupportV1 AEGIS.RHKreinSplineContinuityV1
open AEGIS.RHKreinSplineL1NormV1 AEGIS.RHKreinSplineDerivativesV1
open AEGIS.RHKreinFourierTaylorBoundV1

def realAngular (f : ℝ → ℂ) (t : ℝ) : ℝ := (angularFourier f t).re

theorem realAngular_contDiff (f : ℝ → ℂ) (hf : HasMomentsUpToEight f) :
    ContDiff ℝ 8 (realAngular f) := by
  have hc : ContDiff ℝ 8 (angularFourier f) :=
    (fourier_contDiff_eight f hf).comp (contDiff_const.mul contDiff_id)
  exact Complex.reCLM.contDiff.comp hc

/-- The angular scaling cancels exactly: there is no residual 2*pi factor. -/
theorem angular_eighth_norm_le_moment (f : ℝ → ℂ) (hf : HasMomentsUpToEight f)
    (t : ℝ) :
    ‖iteratedDeriv 8 (angularFourier f) t‖ ≤ ∫ x : ℝ, |x| ^ 8 * ‖f x‖ := by
  have hn (x : ℝ) :
      ‖((-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8) • f x‖ =
        (2 * Real.pi) ^ 8 * (|x| ^ 8 * ‖f x‖) := by
    norm_num [norm_smul, norm_pow, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have hs : |angularScale| ^ 8 * (2 * Real.pi) ^ 8 = 1 := by
    rw [← mul_pow]
    have h : |angularScale| * (2 * Real.pi) = 1 := by
      simp only [angularScale, abs_neg, abs_inv,
        abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact inv_mul_cancel₀ (by positivity)
    rw [h, one_pow]
  calc
    ‖iteratedDeriv 8 (angularFourier f) t‖ ≤
        |angularScale| ^ 8 * ∫ x : ℝ,
          ‖((-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8) • f x‖ :=
      angular_eighth_derivative_norm_le f hf t
    _ = ∫ x : ℝ, |x| ^ 8 * ‖f x‖ := by
      simp_rw [hn]
      rw [integral_const_mul, ← mul_assoc, hs, one_mul]

/-- Taking the real part commutes with the eighth ordinary derivative. -/
theorem realAngular_eighth_le_moment (f : ℝ → ℂ) (hf : HasMomentsUpToEight f)
    (t : ℝ) :
    |iteratedDeriv 8 (realAngular f) t| ≤ ∫ x : ℝ, |x| ^ 8 * ‖f x‖ := by
  have hc : ContDiff ℝ 8 (angularFourier f) :=
    (fourier_contDiff_eight f hf).comp (contDiff_const.mul contDiff_id)
  have he : iteratedDeriv 8 (realAngular f) t =
      (iteratedDeriv 8 (angularFourier f) t).re := by
    change iteratedFDeriv ℝ 8 (Complex.reCLM ∘ angularFourier f) t (fun _ => 1) = _
    rw [Complex.reCLM.iteratedFDeriv_comp_left hc.contDiffAt (by norm_num)]
    rfl
  rw [he]
  exact (Complex.abs_re_le_norm _).trans (angular_eighth_norm_le_moment f hf t)

/-- Positive triangular hat of the original width and center. -/
def hatPacket (j : Fin 199) (x : ℝ) : ℂ :=
  (1 / 50 : ℂ) * splineCore (1 / 50) 1 (x - hatCenter j)

theorem hatPacket_continuous (j : Fin 199) : Continuous (hatPacket j) := by
  have hc := (splineCore_contDiff (by norm_num : (0 : ℝ) ≤ 1 / 50) 0).continuous
  exact continuous_const.mul (hc.comp (continuous_id.sub continuous_const))

theorem hatPacket_compact (j : Fin 199) : HasCompactSupport (hatPacket j) := by
  have hs := (splineCore_hasCompactSupport (1 / 50) 1).comp_homeomorph
    (Homeomorph.addRight (-hatCenter j))
  have ht : HasCompactSupport (fun x : ℝ => splineCore (1 / 50) 1 (x - hatCenter j)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using hs
  exact ht.mul_left

private theorem hatPacket_integrable (j : Fin 199) : Integrable (hatPacket j) :=
  (hatPacket_continuous j).integrable_of_hasCompactSupport (hatPacket_compact j)

/-- Its L1 mass is bounded by its width, not by an unproved pointwise surrogate. -/
theorem hatPacket_L1_le (j : Fin 199) : (∫ x : ℝ, ‖hatPacket j x‖) ≤ 1 / 50 := by
  have hn (x : ℝ) : ‖hatPacket j x‖ =
      (1 / 50 : ℝ) * ‖splineCore (1 / 50) 1 (x - hatCenter j)‖ := by
    simp only [hatPacket, norm_mul]
    norm_num
  calc
    (∫ x : ℝ, ‖hatPacket j x‖) =
        (1 / 50 : ℝ) * ∫ x : ℝ, ‖splineCore (1 / 50) 1 x‖ := by
      simp_rw [hn]
      rw [integral_const_mul,
        integral_sub_right_eq_self (fun x : ℝ => ‖splineCore (1 / 50) 1 x‖) (hatCenter j)]
    _ ≤ (1 / 50 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (integral_norm_splineCore_le_one (by norm_num) 1) (by norm_num)
    _ = 1 / 50 := mul_one _

/-- The exact hat part of the certificate's eighth-moment budget. -/
theorem hatPacket_weighted_eighth_L1 (j : Fin 199) :
    Integrable (fun x : ℝ => |x| ^ 8 * ‖hatPacket j x‖) ∧
      (∫ x : ℝ, |x| ^ 8 * ‖hatPacket j x‖) ≤
        (1 / 50) * (hatCenter j + 1 / 50) ^ 8 := by
  have hi := hatPacket_integrable j
  have hb (x : ℝ) : |x| ^ 8 * ‖hatPacket j x‖ ≤
      (hatCenter j + 1 / 50) ^ 8 * ‖hatPacket j x‖ := by
    by_cases hz : hatPacket j x = 0
    · simp [hz]
    · have hz' : splineCore (1 / 50) 1 (x - hatCenter j) ≠ 0 := by
        intro h
        exact hz (by rw [hatPacket, h, mul_zero])
      have hx := splineCore_support (1 / 50) 1 (x - hatCenter j) hz'
      norm_num at hx
      have hj : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
      have hc : (1 / 50 : ℝ) ≤ hatCenter j := by unfold hatCenter; linarith
      have hx0 : 0 ≤ x := by linarith [hx.1]
      rw [abs_of_nonneg hx0]
      gcongr
      linarith [hx.2]
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |x| ^ 8 * ‖hatPacket j x‖) volume :=
    (continuous_abs.pow 8).aestronglyMeasurable.mul hi.norm.aestronglyMeasurable
  have hw : Integrable (fun x : ℝ => |x| ^ 8 * ‖hatPacket j x‖) := by
    refine (hi.norm.const_mul ((hatCenter j + 1 / 50) ^ 8)).mono' hmeas ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb x
  refine ⟨hw, ?_⟩
  calc
    (∫ x : ℝ, |x| ^ 8 * ‖hatPacket j x‖) ≤
        ∫ x : ℝ, (hatCenter j + 1 / 50) ^ 8 * ‖hatPacket j x‖ :=
      integral_mono hw (hi.norm.const_mul _) hb
    _ = (hatCenter j + 1 / 50) ^ 8 * ∫ x : ℝ, ‖hatPacket j x‖ := integral_const_mul _ _
    _ ≤ (hatCenter j + 1 / 50) ^ 8 * (1 / 50) :=
      mul_le_mul_of_nonneg_left (hatPacket_L1_le j) (by positivity)
    _ = (1 / 50) * (hatCenter j + 1 / 50) ^ 8 := mul_comm _ _

def edgePacket (j : Fin 5) : ℝ → ℂ := deriv^[j.val] (spline19 (4 / 5) (1 / 1000))

private theorem edgePacket_continuous (j : Fin 5) : Continuous (edgePacket j) :=
  (spline19_derivative_contDiff (4 / 5) (by norm_num) j.val (by omega)).continuous

private theorem edgePacket_compact (j : Fin 5) : HasCompactSupport (edgePacket j) := by
  apply HasCompactSupport.intro (K := Icc (4 / 5) (4 / 5 + 19 * (1 / 1000))) isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (spline19_derivative_support (4 / 5) (1 / 1000) j.val (subset_closure hn))

private theorem hat_moments (j : Fin 199) : HasMomentsUpToEight (hatPacket j) :=
  hasMomentsUpToEight_of_continuous_compact _ (hatPacket_continuous j) (hatPacket_compact j)

private theorem edge_moments (j : Fin 5) : HasMomentsUpToEight (edgePacket j) :=
  hasMomentsUpToEight_of_continuous_compact _ (edgePacket_continuous j) (edgePacket_compact j)

private theorem fourier_const_mul (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

private theorem realAngular_hat (j : Fin 199) (t : ℝ) :
    realAngular (hatPacket j) t =
      (1 / 50) * Real.sinc (t / 100) ^ 2 * Real.cos (t * hatCenter j) := by
  unfold realAngular angularFourier hatPacket
  rw [angularScale_mul, fourier_const_mul, fourier_translate_angular,
    splineCore_fourier (by norm_num : (0 : ℝ) < 1 / 50)]
  rw [show (1 / 50 : ℝ) * t / 2 = t / 100 by ring]
  norm_num [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.exp_re]
  ring

private theorem realAngular_edge (j : Fin 5) (t : ℝ) :
    (-1 : ℝ) ^ (j.val / 2) * realAngular (edgePacket j) t =
      Real.sinc (t / 2000) ^ 19 * t ^ j.val *
        (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
         else Real.sin (t * (1619 / 2000))) := by
  unfold realAngular angularFourier edgePacket
  rw [angularScale_mul, spline19_derivative_fourier _ (by norm_num) _ (by omega)]
  rw [show (4 / 5 : ℝ) + 19 * (1 / 1000) / 2 = 1619 / 2000 by norm_num,
    show (1 / 1000 : ℝ) * t / 2 = t / 2000 by ring]
  have hr (z : ℂ) (r : ℝ) : (z * (r : ℂ) ^ 19).re = z.re * r ^ 19 := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hr]
  calc
    _ = Real.sinc (t / 2000) ^ 19 *
        ((-1 : ℝ) ^ (j.val / 2) *
          (((-Complex.I * (t : ℂ)) ^ j.val) *
            Complex.exp (((t * (1619 / 2000) : ℝ) : ℂ) * Complex.I)).re) := by ring
    _ = _ := by rw [certificate_derivative_parity]; ring

/-- Equality to the actual extracted correctionSymbol, with both scaling factors. -/
theorem correctionSymbol_eq_columns : correctionSymbol = fun t : ℝ =>
    (∑ j : Fin 199, (2 * (hatCoefficient j : ℝ)) * realAngular (hatPacket j) t) +
      ∑ j : Fin 5, ((splineCoefficient j : ℝ) * (-1 : ℝ) ^ (j.val / 2)) *
        realAngular (edgePacket j) t := by
  funext t
  unfold correctionSymbol
  simp_rw [mul_assoc (splineCoefficient _ : ℝ), realAngular_hat, realAngular_edge]
  simp only [Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

private theorem columns_contDiff {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a : ι → ℝ) (hc : ∀ i, ContDiff ℝ 8 (f i)) :
    ContDiff ℝ 8 (fun t => ∑ i, a i * f i t) :=
  ContDiff.sum (fun i _ => contDiff_const.mul (hc i))

private theorem column_sum_eighth_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a B : ι → ℝ) (hc : ∀ i, ContDiff ℝ 8 (f i))
    (hb : ∀ i t, |iteratedDeriv 8 (f i) t| ≤ B i) (t : ℝ) :
    |iteratedDeriv 8 (fun t => ∑ i, a i * f i t) t| ≤ ∑ i, |a i| * B i := by
  rw [iteratedDeriv_fun_sum (fun i _ => (contDiff_const.mul (hc i)).contDiffAt)]
  simp_rw [iteratedDeriv_const_mul_field]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb i t) (abs_nonneg _)

def m8Real : ℝ :=
  (∑ j : Fin 199, 2 * (1 / 50) * |(hatCoefficient j : ℝ)| *
    (hatCenter j + 1 / 50) ^ 8) +
  ∑ j : Fin 5, |(splineCoefficient j : ℝ)| * 2000 ^ j.val * (819 / 1000) ^ 8

theorem correctionSymbol_contDiff_eight : ContDiff ℝ 8 correctionSymbol := by
  rw [correctionSymbol_eq_columns]
  exact (columns_contDiff _ _ (fun j => realAngular_contDiff _ (hat_moments j))).add
    (columns_contDiff _ _ (fun j => realAngular_contDiff _ (edge_moments j)))

/-- Full analytic eighth-derivative bound for the exact real correction symbol. -/
theorem correctionSymbol_eighth_derivative_le (t : ℝ) :
    |iteratedDeriv 8 correctionSymbol t| ≤ m8Real := by
  have ch (j : Fin 199) := realAngular_contDiff _ (hat_moments j)
  have ce (j : Fin 5) := realAngular_contDiff _ (edge_moments j)
  have bh (j : Fin 199) (t : ℝ) : |iteratedDeriv 8 (realAngular (hatPacket j)) t| ≤
      (1 / 50) * (hatCenter j + 1 / 50) ^ 8 :=
    (realAngular_eighth_le_moment _ (hat_moments j) t).trans (hatPacket_weighted_eighth_L1 j).2
  have be (j : Fin 5) (t : ℝ) : |iteratedDeriv 8 (realAngular (edgePacket j)) t| ≤
      2000 ^ j.val * (819 / 1000) ^ 8 :=
    (realAngular_eighth_le_moment _ (edge_moments j) t).trans
      (certificate_spline_columns_weighted_eighth_L1 j).2
  rw [correctionSymbol_eq_columns,
    iteratedDeriv_fun_add (columns_contDiff _ _ ch).contDiffAt (columns_contDiff _ _ ce).contDiffAt]
  apply (abs_add_le _ _).trans
  refine (add_le_add (column_sum_eighth_bound _ _ _ ch bh t)
    (column_sum_eighth_bound _ _ _ ce be t)).trans_eq ?_
  unfold m8Real
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [abs_mul]
    norm_num
    ring
  · apply Finset.sum_congr rfl
    intro j _
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    ring

/-- Rational arithmetic and the analytic real budget describe exactly the same number. -/
theorem m8Real_eq_certificateM8Q : m8Real = (certificateM8Q : ℝ) := by
  unfold m8Real certificateM8Q hatCenter hatCenterQ
  push_cast
  apply congrArg₂ (fun x y : ℝ => x + y)
  · rfl
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_assoc, ← div_pow]
    norm_num

/-- The serialized rational M8 is an unconditional bound at every real frequency.
No finite-cell lower endpoint is used as a premise. -/
theorem correctionSymbol_eighth_derivative_le_serialized (t : ℝ) :
    |iteratedDeriv 8 correctionSymbol t| ≤ (serializedM8Q : ℝ) := by
  have h := correctionSymbol_eighth_derivative_le t
  rwa [m8Real_eq_certificateM8Q, certificateM8_eq_serialized_v1] at h

end AEGIS.RHKreinCorrectionM8BoundV1

#print axioms AEGIS.RHKreinCorrectionM8BoundV1.realAngular_contDiff
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.angular_eighth_norm_le_moment
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.realAngular_eighth_le_moment
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.hatPacket_L1_le
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.hatPacket_weighted_eighth_L1
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.correctionSymbol_eq_columns
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.correctionSymbol_contDiff_eight
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.correctionSymbol_eighth_derivative_le
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.m8Real_eq_certificateM8Q
#print axioms AEGIS.RHKreinCorrectionM8BoundV1.correctionSymbol_eighth_derivative_le_serialized
