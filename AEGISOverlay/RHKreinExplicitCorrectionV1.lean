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

import AEGISOverlay.RHKreinSplineDerivativesV1
import RHKreinGenuineCertificateV1

/-!
# The exact genuine-function correction for the order-19 certificate

The rational coefficients are copied exactly from
`research/rh/krein_order19_v1/certificate.json`. The 199 hat columns are
translated order-two normalized box convolutions multiplied by their width.
The five edge columns are ordinary derivatives of the genuine order-19 spline.
Hermitian reflection and the factors `(-1)^(j/2)/2` give exactly the sine/cosine
convention of the certificate. The pointwise symbol inequality is an explicit
remaining hypothesis, not a numerical premise asserted as a theorem.
-/

open Set MeasureTheory Complex FourierTransform
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinExplicitCorrectionV1

open AEGIS.RHKreinSplineSupportV1 AEGIS.RHKreinSplineContinuityV1
open AEGIS.RHKreinSplineFourierIntegrableV1 AEGIS.RHKreinSplineDerivativesV1

/-- Exact rational hat coefficients in increasing center order. -/
def hatCoefficient : Fin 199 → ℚ :=
  ![-100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -190093321285891/2500000000,
    100000,
    100000,
    100000,
    100000,
    29666418987513/2500000000,
    -100000,
    -100000,
    -100000,
    -117731535372369/2500000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    50425751969473/2000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    515177348963881/10000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    100000,
    100000,
    100000,
    -51422462806047/1000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -116660983646653/1250000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -166526644754763/10000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -118048813499739/1250000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    2953816304371/1000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    7920263226739/1000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -164690278619151/10000000000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    6934524025071/80000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    730856184163993/10000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    414340348739593/10000000000,
    100000,
    100000,
    100000,
    100000,
    378057512105339/10000000000,
    -100000,
    -100000,
    -100000,
    -618999438984917/10000000000,
    100000,
    100000,
    -100000,
    -100000,
    -101839738853771/2500000000,
    100000,
    100000,
    100000,
    100000,
    86995914959651/1000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    100000,
    100000,
    -25574621798421/400000000,
    -100000,
    -469702038657277/10000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -247976924265647/5000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    296561423630109/10000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -373908230082811/5000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -186287944404417/10000000000,
    100000,
    100000,
    100000,
    100000,
    -16872084697291/5000000000,
    -100000,
    -100000,
    -100000,
    200108515493551/10000000000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    -100000,
    -100000,
    730445128203157/10000000000,
    100000,
    100000,
    19841790224691/2000000000,
    -47556077772879/5000000000,
    100000,
    -886028847662807/10000000000,
    -100000,
    -100000,
    110857698784947/10000000000,
    100000,
    100000,
    -431069777588841/5000000000]

/-- Exact rational derivative coefficients in derivative order zero through four. -/
def splineCoefficient : Fin 5 → ℚ :=
  ![234102120892757/5000000000,
    -12240399939171/2500000000,
    -2918648959121/10000000000,
    123578990441/10000000000,
    9711997751/10000000000]

def hatCenter (j : Fin 199) : ℝ := ((j.val : ℝ) + 41) / 50

/-- The explicit angular Fourier correction used by the exact certificate. -/
def correctionSymbol (t : ℝ) : ℝ :=
  (2 / 50) * Real.sinc (t / 100) ^ 2 *
    (∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j)) +
  Real.sinc (t / 2000) ^ 19 *
    (∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
      (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
       else Real.sin (t * (1619 / 2000))))

private def reflected (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x + (starRingEnd ℂ) (f (-x))

private theorem reflected_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (reflected f) :=
  hf.add (continuous_conj.comp (hf.comp continuous_neg))

private theorem reflected_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (reflected f) := by
  have hi : Integrable (fun x : ℝ => (starRingEnd ℂ) (f (-x))) := by
    simpa using (Complex.conjLIE.toContinuousLinearMap).integrable_comp hf.comp_neg
  exact hf.add hi

private theorem reflected_hasCompactSupport {f : ℝ → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (reflected f) := by
  have hneg : HasCompactSupport (fun x : ℝ => f (-x)) := by
    have h := hf.comp_homeomorph (Homeomorph.neg ℝ)
    simpa [Function.comp_def] using h
  have hconj : HasCompactSupport (fun x : ℝ => (starRingEnd ℂ) (f (-x))) := by
    have h := hneg.comp_left (map_zero (starRingEnd ℂ))
    simpa [Function.comp_def] using h
  unfold reflected
  exact hf.add hconj

private theorem fourier_add (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (ξ : ℝ) : 𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  exact congrArg (fun F : ℝ → ℂ => F ξ)
    (VectorFourier.fourierIntegral_add (e := Real.fourierChar)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg)

private theorem fourier_const_mul (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

private theorem fourier_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    (hf : ∀ j, Integrable (f j)) (ξ : ℝ) :
    𝓕 (fun x => ∑ j, f j x) ξ = ∑ j, 𝓕 (f j) ξ := by
  simp only [Real.fourier_eq, Finset.smul_sum]
  exact integral_finsetSum _ (fun j _ => (Real.fourierIntegral_convergent_iff ξ).2 (hf j))

private theorem reflected_fourier {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    𝓕 (reflected f) ξ = 𝓕 f ξ + (starRingEnd ℂ) (𝓕 f ξ) := by
  have hi : Integrable (fun x : ℝ => (starRingEnd ℂ) (f (-x))) := by
    simpa using (Complex.conjLIE.toContinuousLinearMap).integrable_comp hf.comp_neg
  change 𝓕 (fun x : ℝ => f x + (starRingEnd ℂ) (f (-x))) ξ =
    𝓕 f ξ + (starRingEnd ℂ) (𝓕 f ξ)
  rw [fourier_add f _ hf hi, AEGIS.RHKreinPairingV13.fourier_conj_neg]

private theorem reflected_fourier_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hF : Integrable (𝓕 f)) : Integrable (𝓕 (reflected f)) := by
  have hi : Integrable (fun ξ : ℝ => (starRingEnd ℂ) (𝓕 f ξ)) := by
    simpa using (Complex.conjLIE.toContinuousLinearMap).integrable_comp hF
  exact (hF.add hi).congr (Filter.Eventually.of_forall fun ξ => (reflected_fourier hf ξ).symm)

private theorem angular_integrable_iff (f : ℝ → ℂ)
    (hf : Integrable (fun t : ℝ => f (-t / (2 * Real.pi)))) : Integrable f := by
  have hp : -(2 * Real.pi) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hi := hf.comp_mul_right' hp
  convert hi using 1
  funext ξ
  field_simp [Real.pi_ne_zero]

/-- One ordinary triangular hat represented by convolution of normalized boxes. -/
def positiveHat (j : Fin 199) (x : ℝ) : ℂ :=
  (1 / 50 : ℂ) * splineCore (1 / 50) 1 (x - hatCenter j)

private theorem positiveHat_continuous (j : Fin 199) : Continuous (positiveHat j) := by
  have hc := (splineCore_contDiff (by norm_num : (0 : ℝ) ≤ 1 / 50) 0).continuous
  exact continuous_const.mul (hc.comp (continuous_id.sub continuous_const))

private theorem positiveHat_integrable (j : Fin 199) : Integrable (positiveHat j) :=
  ((splineCore_integrable (1 / 50) 1).comp_sub_right (hatCenter j)).const_mul _

private theorem positiveHat_hasCompactSupport (j : Fin 199) :
    HasCompactSupport (positiveHat j) := by
  have hb := splineCore_hasCompactSupport (1 / 50) 1
  have ht : HasCompactSupport
      (fun x : ℝ => splineCore (1 / 50) 1 (x - hatCenter j)) := by
    have h := hb.comp_homeomorph (Homeomorph.addRight (-hatCenter j))
    simpa [Function.comp_def, sub_eq_add_neg] using h
  unfold positiveHat
  exact ht.mul_left

private theorem positiveHat_fourier (j : Fin 199) (t : ℝ) :
    𝓕 (positiveHat j) (-t / (2 * Real.pi)) =
      (1 / 50 : ℂ) * Complex.exp (((t * hatCenter j : ℝ) : ℂ) * Complex.I) *
        (Real.sinc (t / 100) : ℂ) ^ 2 := by
  unfold positiveHat
  rw [fourier_const_mul, fourier_translate_angular,
    splineCore_fourier (by norm_num : (0 : ℝ) < 1 / 50)]
  rw [show (1 / 50 : ℝ) * t / 2 = t / 100 by ring]
  ring

private theorem positiveHat_fourier_integrable (j : Fin 199) :
    Integrable (𝓕 (positiveHat j)) := by
  apply angular_integrable_iff
  have hs : Integrable (fun t : ℝ => (Real.sinc (t / 100) : ℂ) ^ 2) := by
    simpa only [div_eq_mul_inv] using
      (sinc_pow_integrable 2 (by norm_num)).comp_mul_right' (by norm_num : (100 : ℝ)⁻¹ ≠ 0)
  have he : Integrable (fun t : ℝ =>
      Complex.exp (((t * hatCenter j : ℝ) : ℂ) * Complex.I) *
        (Real.sinc (t / 100) : ℂ) ^ 2) := by
    refine hs.norm.mono' ?_ ?_
    · have hc : Continuous (fun t : ℝ =>
          Complex.exp (((t * hatCenter j : ℝ) : ℂ) * Complex.I) *
            (Real.sinc (t / 100) : ℂ) ^ 2) := by fun_prop
      exact hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by simp [Complex.norm_exp]
  exact (he.const_mul (1 / 50 : ℂ)).congr (Filter.Eventually.of_forall fun t => by
    simpa [mul_assoc] using (positiveHat_fourier j t).symm)

private theorem positiveHat_zero (j : Fin 199) {x : ℝ} (hx : |x| < 4 / 5) :
    positiveHat j x = 0 := by
  have hz : splineCore (1 / 50) 1 (x - hatCenter j) = 0 := by
    by_contra hn
    have hs := (splineCore_support (1 / 50) 1 (x - hatCenter j) hn).1
    have hj : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    dsimp [hatCenter] at hs
    norm_num at hs
    linarith [le_abs_self x]
  have hz' : splineCore (50⁻¹ : ℝ) 1 (x - hatCenter j) = 0 := by
    simpa only [one_div] using hz
  simp [positiveHat, one_div, hz']

/-- The Hermitian pair of triangular hats centered at opposite locations. -/
def hatColumn (j : Fin 199) : ℝ → ℂ := reflected (positiveHat j)

/-- The normalized genuine derivative column, including its parity sign. -/
def splineColumn (j : Fin 5) (x : ℝ) : ℂ :=
  ((-1 : ℂ) ^ (j.val / 2) / 2) *
    reflected (deriv^[j.val] (spline19 (4 / 5) (1 / 1000))) x

private theorem edge_integrable (j : Fin 5) :
    Integrable (deriv^[j.val] (spline19 (4 / 5) (1 / 1000))) :=
  spline19_derivative_integrable _ (by norm_num) _ (by omega)

private theorem edge_zero (j : Fin 5) {x : ℝ} (hx : |x| < 4 / 5) :
    deriv^[j.val] (spline19 (4 / 5) (1 / 1000)) x = 0 := by
  by_contra hn
  have hs := (spline19_derivative_support (4 / 5) (1 / 1000) j.val
    (subset_closure hn)).1
  linarith [le_abs_self x]

private theorem hatColumn_fourier_re (j : Fin 199) (t : ℝ) :
    (𝓕 (hatColumn j) (-t / (2 * Real.pi))).re =
      (2 / 50) * Real.sinc (t / 100) ^ 2 * Real.cos (t * hatCenter j) := by
  rw [hatColumn, reflected_fourier (positiveHat_integrable j), positiveHat_fourier]
  norm_num [← Complex.ofReal_pow, Complex.add_re, Complex.conj_re, Complex.mul_re,
    Complex.mul_im, Complex.exp_re]
  ring

private theorem splineColumn_fourier_re (j : Fin 5) (t : ℝ) :
    (𝓕 (splineColumn j) (-t / (2 * Real.pi))).re =
      Real.sinc (t / 2000) ^ 19 * t ^ j.val *
        (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
         else Real.sin (t * (1619 / 2000))) := by
  unfold splineColumn
  rw [fourier_const_mul, reflected_fourier (edge_integrable j),
    spline19_derivative_fourier _ (by norm_num) _ (by omega)]
  have hc : (4 / 5 : ℝ) + 19 * (1 / 1000) / 2 = 1619 / 2000 := by norm_num
  have hs : (1 / 1000 : ℝ) * t / 2 = t / 2000 := by ring
  rw [hc, hs]
  have he (z : ℂ) (r : ℝ) :
      (((-1 : ℂ) ^ (j.val / 2) / 2) * (z * (r : ℂ) ^ 19 +
        (starRingEnd ℂ) (z * (r : ℂ) ^ 19))).re =
      r ^ 19 * (((-1 : ℂ) ^ (j.val / 2) / 2) *
        (z + (starRingEnd ℂ) z)).re := by
    have hz : ((-1 : ℂ) ^ (j.val / 2) / 2) *
        (z * (r : ℂ) ^ 19 + (starRingEnd ℂ) (z * (r : ℂ) ^ 19)) =
        ((r ^ 19 : ℝ) : ℂ) *
          (((-1 : ℂ) ^ (j.val / 2) / 2) * (z + (starRingEnd ℂ) z)) := by
      simp only [map_mul, map_pow, Complex.conj_ofReal]
      push_cast
      ring
    calc
      _ = (((r ^ 19 : ℝ) : ℂ) *
          (((-1 : ℂ) ^ (j.val / 2) / 2) *
            (z + (starRingEnd ℂ) z))).re := congrArg Complex.re hz
      _ = _ := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
  rw [he, certificate_reflected_derivative_parity]
  ring

/-- A finite linear combination of genuine compactly supported functions. -/
def correction (x : ℝ) : ℂ :=
  (∑ j : Fin 199, ((hatCoefficient j : ℝ) : ℂ) * hatColumn j x) +
    ∑ j : Fin 5, ((splineCoefficient j : ℝ) : ℂ) * splineColumn j x

private theorem hatColumn_integrable (j : Fin 199) : Integrable (hatColumn j) :=
  reflected_integrable (positiveHat_integrable j)

private theorem splineColumn_integrable (j : Fin 5) : Integrable (splineColumn j) :=
  (reflected_integrable (edge_integrable j)).const_mul _

private theorem hatColumn_hasCompactSupport (j : Fin 199) :
    HasCompactSupport (hatColumn j) :=
  reflected_hasCompactSupport (positiveHat_hasCompactSupport j)

private theorem edge_hasCompactSupport (j : Fin 5) :
    HasCompactSupport (deriv^[j.val] (spline19 (4 / 5) (1 / 1000))) := by
  apply HasCompactSupport.intro
    (K := Set.Icc (4 / 5) (4 / 5 + 19 * (1 / 1000))) isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (spline19_derivative_support (4 / 5) (1 / 1000) j.val
    (subset_closure hn))

private theorem splineColumn_hasCompactSupport (j : Fin 5) :
    HasCompactSupport (splineColumn j) := by
  unfold splineColumn
  exact (reflected_hasCompactSupport (edge_hasCompactSupport j)).mul_left

set_option maxHeartbeats 2000000 in
private theorem finiteSum_hasCompactSupport {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x : ℝ => ∑ i, f i x) := by
  classical
  have hs : HasCompactSupport (∑ i, f i) :=
    (HasCompactSupport.addSubmonoid ℝ ℂ).sum_mem (fun i _ => hf i)
  have hsum : (fun x : ℝ => ∑ i, f i x) = (∑ i, f i) := by
    funext x
    simp
  rw [hsum]
  exact hs

/-- The correction is continuous despite containing derivative columns. -/
theorem correction_continuous : Continuous correction := by
  have hh (j : Fin 199) : Continuous (hatColumn j) :=
    reflected_continuous (positiveHat_continuous j)
  have hs (j : Fin 5) : Continuous (splineColumn j) := by
    have hc := (spline19_derivative_contDiff (4 / 5)
      (by norm_num : (0 : ℝ) ≤ 1 / 1000) j.val (by omega)).continuous
    exact continuous_const.mul (reflected_continuous hc)
  unfold correction
  exact (continuous_finsetSum _ fun j _ => continuous_const.mul (hh j)).add
    (continuous_finsetSum _ fun j _ => continuous_const.mul (hs j))

/-- Lebesgue integrability of the concrete correction. -/
theorem correction_integrable : Integrable correction := by
  exact (integrable_finsetSum _ fun j _ =>
    (hatColumn_integrable j).const_mul ((hatCoefficient j : ℝ) : ℂ)).add
    (integrable_finsetSum _ fun j _ =>
      (splineColumn_integrable j).const_mul ((splineCoefficient j : ℝ) : ℂ))

set_option maxHeartbeats 2000000 in
/-- The explicit correction is genuinely compactly supported. -/
theorem correction_hasCompactSupport : HasCompactSupport correction := by
  have hh : HasCompactSupport (fun x : ℝ =>
      ∑ j : Fin 199, ((hatCoefficient j : ℝ) : ℂ) * hatColumn j x) := by
    apply finiteSum_hasCompactSupport
    intro j
    exact (hatColumn_hasCompactSupport j).mul_left
  have hs : HasCompactSupport (fun x : ℝ =>
      ∑ j : Fin 5, ((splineCoefficient j : ℝ) : ℂ) * splineColumn j x) := by
    apply finiteSum_hasCompactSupport
    intro j
    exact (splineColumn_hasCompactSupport j).mul_left
  unfold correction
  exact hh.add hs

/-- The correction vanishes on the entire forbidden window. -/
theorem correction_zero_in_window (x : ℝ) (hx : |x| < 4 / 5) : correction x = 0 := by
  have hn : |-x| < 4 / 5 := by simpa using hx
  have hh (j : Fin 199) : hatColumn j x = 0 := by
    simp [hatColumn, reflected, positiveHat_zero j hx, positiveHat_zero j hn]
  have hs (j : Fin 5) : splineColumn j x = 0 := by
    have hxp :
        deriv^[j.val] (spline19 (4 / 5) (1000⁻¹ : ℝ)) x = 0 := by
      simpa only [one_div] using (edge_zero j hx)
    have hxn :
        deriv^[j.val] (spline19 (4 / 5) (1000⁻¹ : ℝ)) (-x) = 0 := by
      simpa only [one_div] using (edge_zero j hn)
    unfold splineColumn reflected
    simp only [one_div]
    rw [hxp, hxn]
    simp
  simp [correction, hh, hs]

private theorem correction_fourier (ξ : ℝ) :
    𝓕 correction ξ =
      (∑ j : Fin 199, ((hatCoefficient j : ℝ) : ℂ) * 𝓕 (hatColumn j) ξ) +
        ∑ j : Fin 5, ((splineCoefficient j : ℝ) : ℂ) * 𝓕 (splineColumn j) ξ := by
  unfold correction
  rw [fourier_add _ _ (integrable_finsetSum _ fun j _ =>
    (hatColumn_integrable j).const_mul _) (integrable_finsetSum _ fun j _ =>
      (splineColumn_integrable j).const_mul _),
    fourier_sum _ (fun j => (hatColumn_integrable j).const_mul _),
    fourier_sum _ (fun j => (splineColumn_integrable j).const_mul _)]
  simp only [fourier_const_mul]

/-- The actual Fourier transform of the correction is integrable. -/
theorem correction_fourier_integrable : Integrable (𝓕 correction) := by
  have hh (j : Fin 199) : Integrable (𝓕 (hatColumn j)) :=
    reflected_fourier_integrable (positiveHat_integrable j) (positiveHat_fourier_integrable j)
  have hs (j : Fin 5) : Integrable (𝓕 (splineColumn j)) := by
    have hi := reflected_fourier_integrable (edge_integrable j)
      (spline19_derivative_fourier_integrable (4 / 5)
        (by norm_num : (0 : ℝ) < 1 / 1000) j.val (by omega))
    exact (hi.const_mul _).congr (Filter.Eventually.of_forall fun ξ => by
      exact (fourier_const_mul _ _ ξ).symm)
  exact ((integrable_finsetSum _ fun j _ => (hh j).const_mul ((hatCoefficient j : ℝ) : ℂ)).add
    (integrable_finsetSum _ fun j _ => (hs j).const_mul ((splineCoefficient j : ℝ) : ℂ))).congr
      (Filter.Eventually.of_forall fun ξ => (correction_fourier ξ).symm)

/-- The exact analytic expression is propositionally bound to the actual
Mathlib Fourier transform, including all reflection and parity factors. -/
theorem correction_fourier_re (t : ℝ) :
    (𝓕 correction (-t / (2 * Real.pi))).re = correctionSymbol t := by
  rw [correction_fourier, Complex.add_re, Complex.re_sum, Complex.re_sum]
  have hh (j : Fin 199) :
      (((hatCoefficient j : ℝ) : ℂ) * 𝓕 (hatColumn j) (-t / (2 * Real.pi))).re =
      (hatCoefficient j : ℝ) * ((2 / 50) * Real.sinc (t / 100) ^ 2 *
        Real.cos (t * hatCenter j)) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hatColumn_fourier_re]
  have hs (j : Fin 5) :
      (((splineCoefficient j : ℝ) : ℂ) * 𝓕 (splineColumn j) (-t / (2 * Real.pi))).re =
      (splineCoefficient j : ℝ) * (Real.sinc (t / 2000) ^ 19 * t ^ j.val *
        (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
         else Real.sin (t * (1619 / 2000)))) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [splineColumn_fourier_re]
  simp only [hh, hs, correctionSymbol, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- This proposition is precisely the remaining pointwise analytic certificate. -/
def PointwiseCertificate : Prop :=
  ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 *
    (AEGIS.RHKreinPrimeSymbolV1.symbol t - 1 / 16) + correctionSymbol t

/-- The explicit certificate implies a `1/16` margin for every actual moment-zero
packet with logarithmic half-width at most `2/5`. -/
theorem actual_zero_quadratic_margin (hcert : PointwiseCertificate)
    (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) :
    (1 / 16) * AEGIS.WeilDisjointEnergyV2.energy g.1 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hlog : 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  apply AEGIS.RHKreinGenuineCertificateV1.zero_quadratic_margin_from_genuine_certificate
    g r a (1 / 16) hr0 hw (by linarith) hm correction
    correction_continuous correction_integrable correction_fourier_integrable
  · intro u hu
    exact correction_zero_in_window u (by linarith)
  · intro t
    rw [correction_fourier_re]
    exact hcert t

end AEGIS.RHKreinExplicitCorrectionV1

#print axioms AEGIS.RHKreinExplicitCorrectionV1.correction_continuous
#print axioms AEGIS.RHKreinExplicitCorrectionV1.correction_integrable
#print axioms AEGIS.RHKreinExplicitCorrectionV1.correction_hasCompactSupport
#print axioms AEGIS.RHKreinExplicitCorrectionV1.correction_zero_in_window
#print axioms AEGIS.RHKreinExplicitCorrectionV1.correction_fourier_integrable
#print axioms AEGIS.RHKreinExplicitCorrectionV1.correction_fourier_re
#print axioms AEGIS.RHKreinExplicitCorrectionV1.actual_zero_quadratic_margin
