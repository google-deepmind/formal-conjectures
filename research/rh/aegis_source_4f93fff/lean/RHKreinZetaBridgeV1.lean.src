import WeilCriticalLineKreinFormV1
import RHKreinFactorV13
import RHKreinCertificateV1
import RHDyadicDiagonalV13

/-!
AEGIS Ω — Krein dual certificate ⇒ nonnegative zeta zero quadratic on a support class (v1).

Connects `RHKreinCertificateV1.certificate_lower_bound` (Fourier side) to the repository zero quadratic
`Σ_ρ Z_ρ(A_g)` through `WeilCriticalLineKreinFormV1.zero_quadratic_krein_form_v1`:

* `mellin_crit`: `Mg(1/2+it) = 𝓕 Gm (t/2π)` with `Gm u = e^{-u/2} g(e^{-u})` (Mathlib `mellin_eq_fourier`);
* `Gm_tsupport`, `Gm_moment_*`: a moment-zero packet of log-half-width `r` gives a smooth `Gm` supported in an
  interval of length `2r` with `∫ e^{∓u/2} Gm = 0`;
* `moment_zero_parametrization` (RHKreinFactorV13): `Gm = χ'' − χ/4`, so `|𝓕Gm|² = W·|𝓕χ|²`;
* for `2r < L ≤ log 3` every prime-power term with `m ≥ 3` pairs to zero (`column_zero`, `j = 0`), and the
  `m = 2` term is the `√2·log 2·cos(t log 2)` in the symbol.

The pointwise certificate inequality is a hypothesis. Not RH.  AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Complex
open scoped ContDiff
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace AEGIS.RHKreinZetaBridgeV1

open AEGIS.WeilCriticalLineKreinFormV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilCriticalLinePrimeV1

/-- The critical-line log profile `u ↦ e^{-u/2} g(e^{-u})`. -/
def Gm (g : WeilCompactSmoothGV1) (u : ℝ) : ℂ :=
  ((Real.exp (-(1 / 2) * u) : ℝ) : ℂ) * g.1 (Real.exp (-u))

theorem mellin_crit (g : WeilCompactSmoothGV1) (t : ℝ) :
    mellin g.1 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 𝓕 (Gm g) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hre : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by simp
  have him : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im = t := by simp
  rw [hre, him]
  congr 1

theorem Nr_eq (g : WeilCompactSmoothGV1) (t : ℝ) :
    Nr g t = Complex.normSq (𝓕 (Gm g) (t / (2 * Real.pi))) := by
  rw [Nr, mellin_crit]

theorem Gm_contDiff (g : WeilCompactSmoothGV1) : ContDiff ℝ ∞ (Gm g) := by
  have hg := g.2.1
  unfold Gm
  refine ContDiff.mul ?_ (hg.comp (Real.contDiff_exp.comp contDiff_neg))
  exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

theorem Gm_eq_logLift (g : WeilCompactSmoothGV1) (u : ℝ) :
    Gm g u = AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 (-u) := by
  simp only [Gm, AEGIS.WeilLogCoordinateIsometryV21.logLift]
  congr 3
  ring

open AEGIS.RHDyadicDiagonalV13 AEGIS.WeilThreeBlockTranslatedPacketsV22 in
theorem Gm_tsupport (g : WeilCompactSmoothGV1) (r a : ℝ) (hw : HalfWidthAt g r a) :
    tsupport (Gm g) ⊆ Set.Icc (-a - r) (-a + r) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have hu' : AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 (-u) ≠ 0 := by
    rw [← Gm_eq_logLift]; exact hu
  have h := hw (subset_tsupport _ hu')
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

theorem fourier_zero_eq (f : ℝ → ℂ) : 𝓕 f 0 = ∫ u, f u := by
  simp [Real.fourier_eq]

theorem mellin_one_eq (g : WeilCompactSmoothGV1) :
    mellin g.1 1 = ∫ u, ((Real.exp (-1 * u) : ℝ) : ℂ) * g.1 (Real.exp (-u)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.one_re, Complex.one_im, zero_div, fourier_zero_eq, Complex.real_smul]

theorem mellin_zero_eq (g : WeilCompactSmoothGV1) :
    mellin g.1 0 = ∫ u, g.1 (Real.exp (-u)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.zero_re, Complex.zero_im, zero_div, fourier_zero_eq, Complex.real_smul,
    neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]

theorem Gm_moment_minus (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∫ u, (Real.exp (-u / 2) : ℂ) * Gm g u = 0 := by
  have h1 : mellin g.1 1 = ∫ x in Set.Ioi (0 : ℝ), g.1 x := by
    simp [mellin]
  rw [mellin_one_eq, hm.2] at h1
  rw [← h1]
  congr 1; funext u
  simp only [Gm]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

theorem Gm_moment_plus (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∫ u, (Real.exp (u / 2) : ℂ) * Gm g u = 0 := by
  have h1 : mellin g.1 0 = ∫ x in Set.Ioi (0 : ℝ), g.1 x / (x : ℂ) := by
    simp only [mellin, zero_sub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [Complex.cpow_neg_one, smul_eq_mul, div_eq_inv_mul]
  rw [mellin_zero_eq, hm.1] at h1
  rw [← h1]
  congr 1; funext u
  simp only [Gm]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  have : u / 2 + -(1 / 2) * u = 0 := by ring
  rw [this, Real.exp_zero, Complex.ofReal_one, one_mul]

theorem fourier_lin (A B : ℝ → ℂ) (hA : Integrable A) (hB : Integrable B) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun u => A u - c * B u) ξ = 𝓕 A ξ - c * 𝓕 B ξ := by
  have iA : Integrable (fun v : ℝ => 𝐞 (-(v * ξ)) • A v) := by
    have h := (VectorFourier.fourierIntegral_convergent_iff (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner ξ).2 hA
    simpa [mul_comm] using h
  have iB : Integrable (fun v : ℝ => 𝐞 (-(v * ξ)) • B v) := by
    have h := (VectorFourier.fourierIntegral_convergent_iff (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner ξ).2 hB
    simpa [mul_comm] using h
  have e : ∀ f : ℝ → ℂ, 𝓕 f ξ = ∫ v, 𝐞 (-(v * ξ)) • f v := fun f => by
    rw [Real.fourier_eq]; congr 1; funext v; simp [mul_comm]
  rw [e, e, e, ← integral_const_mul, ← integral_sub iA (iB.const_mul c)]
  congr 1; funext v
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- Weight `W(t) = (t² + 1/4)²`. -/
def Wt (t : ℝ) : ℝ := (t ^ 2 + 1 / 4) ^ 2

/-- Moment-zero packets factor through `χ'' − χ/4`, and `Nr g t = W(t)·|𝓕χ(t/2π)|²`. -/
theorem Nr_factor (g : WeilCompactSmoothGV1) (r a : ℝ) (hr : 0 ≤ r) (hw : HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) :
    ∃ chi : ℝ → ℂ, ContDiff ℝ ∞ chi ∧ tsupport chi ⊆ Set.Icc (-a - r) (-a + r) ∧
      ∀ t, Nr g t = Wt t * Complex.normSq (𝓕 chi (t / (2 * Real.pi))) := by
  obtain ⟨chi, hc, hs, hode⟩ := AEGIS.RHKreinFactorV13.moment_zero_parametrization (Gm g)
    (-a - r) (-a + r) (by linarith) (Gm_contDiff g) (Gm_tsupport g r a hw)
    (Gm_moment_minus g hm) (Gm_moment_plus g hm)
  refine ⟨chi, hc, hs, fun t => ?_⟩
  have hts : tsupport chi ⊆ Set.Ioo (-a - r - 1) (-a + r + 1) :=
    hs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hint := AEGIS.RHKreinDeltaPairingV1.iteratedDeriv_integrable chi hc _ _ hts
  have hall : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv n chi) :=
    fun n _ => hint n
  have h2 : iteratedDeriv 2 chi = deriv (deriv chi) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hG : Gm g = fun u => iteratedDeriv 2 chi u - (1 / 4 : ℂ) * chi u := by
    funext u; rw [hode u, h2]
  have hF := Real.fourier_iteratedDeriv (N := ⊤) (n := 2) hc hall le_top
  have h0 : Integrable chi := by simpa using hint 0
  rw [Nr_eq, hG, fourier_lin _ _ (hint 2) h0, hF]
  set ξ := t / (2 * Real.pi)
  have hξ : 2 * Real.pi * ξ = t := by
    simp only [ξ]; field_simp
  have hfac : (2 * (Real.pi : ℂ) * I * (ξ : ℂ)) ^ 2 • 𝓕 chi ξ - (1 / 4 : ℂ) * 𝓕 chi ξ =
      ((-(t ^ 2 + 1 / 4) : ℝ) : ℂ) * 𝓕 chi ξ := by
    rw [smul_eq_mul, ← hξ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfac, Complex.normSq_mul, Complex.normSq_ofReal, Wt]
  ring

theorem two_pi_div (x : ℝ) : 2 * Real.pi * x / (2 * Real.pi) = x := by
  field_simp

/-- **Prime-power terms beyond the window vanish**: if `2r < c` then `∫ cos(t c)·Nr g t dt = 0`. -/
theorem cos_pair_zero (g : WeilCompactSmoothGV1) (r a : ℝ) (hw : HalfWidthAt g r a)
    (c : ℝ) (hc : 2 * r < c) :
    ∫ t, Real.cos (t * c) * Nr g t = 0 := by
  set ε := (c - 2 * r) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hts : tsupport (Gm g) ⊆ Set.Ioo (-a - r - ε) (-a + r + ε) :=
    (Gm_tsupport g r a hw).trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hL : (-a + r + ε) - (-a - r - ε) ≤ c := by rw [hε]; linarith
  have h0 := AEGIS.RHKreinCertificateV1.column_zero (Gm g) (Gm_contDiff g) _ _ hts 0 c hL
  have hi := AEGIS.RHKreinCertificateV1.column_integrable (Gm g) (Gm_contDiff g) _ _ hts 0 c
  have hre : ∫ ν, Real.cos (2 * Real.pi * ν * c) * Complex.normSq (𝓕 (Gm g) ν) = 0 := by
    have h := integral_re hi
    rw [h0] at h
    simp only [RCLike.re_to_complex, Complex.zero_re] at h
    rw [← h]
    congr 1; funext ν
    simp only [pow_zero, one_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    ring
  have hs := MeasureTheory.Measure.integral_comp_mul_left
    (fun t => Real.cos (t * c) * Nr g t) (2 * Real.pi)
  have hL' : (∫ x : ℝ, Real.cos (2 * Real.pi * x * c) * Nr g (2 * Real.pi * x)) = 0 := by
    rw [← hre]
    congr 1; funext x
    rw [Nr_eq, two_pi_div]
  rw [hL'] at hs
  have hne : |(2 * Real.pi)⁻¹| ≠ 0 := by positivity
  rw [smul_eq_mul] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left hne

/-- `Re ψ(1/4 + it/2)`. -/
def Psi (t : ℝ) : ℝ := (Complex.digamma (zt t)).re

theorem Psi_even (t : ℝ) : Psi (-t) = Psi t := by
  simp only [Psi]
  rw [← conj_zt, digamma_conj_v1 _ (zt_re t), Complex.conj_re]

theorem Nr_nonneg (g : WeilCompactSmoothGV1) (t : ℝ) : 0 ≤ Nr g t := Complex.normSq_nonneg _

theorem psiNr_integrable (g : WeilCompactSmoothGV1) :
    Integrable (fun t => (Psi t + Real.eulerMascheroniConstant) * Nr g t) := by
  have hA := (archF_integrable g).re
  have hN := Nr_integrable g
  have hNn : Integrable (fun t => Nr g (-t)) := hN.comp_neg
  have heq : ∀ t, (Psi t + Real.eulerMascheroniConstant) * Nr g t = (archF g t).re * (Nr g t / (Nr g t + Nr g (-t))) := by
    intro t
    rw [archF_re]
    by_cases h : Nr g t + Nr g (-t) = 0
    · have h0 : Nr g t = 0 := by linarith [Nr_nonneg g t, Nr_nonneg g (-t)]
      rw [h0]; simp
    · rw [Psi]; field_simp
  refine Integrable.mono' hA.norm ?_ ?_
  · have hm : AEMeasurable (fun t => (archF g t).re * (Nr g t / (Nr g t + Nr g (-t)))) :=
      hA.aemeasurable.mul (hN.aemeasurable.div (hN.aemeasurable.add hNn.aemeasurable))
    refine hm.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun t => (heq t).symm)
  · refine Filter.Eventually.of_forall fun t => ?_
    show ‖_‖ ≤ ‖(archF g t).re‖
    rw [archF_re, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Nr_nonneg g t), abs_of_nonneg (add_nonneg (Nr_nonneg g t) (Nr_nonneg g (-t)))]
    rw [Psi]
    exact mul_le_mul_of_nonneg_left (by linarith [Nr_nonneg g (-t)]) (abs_nonneg _)

theorem cosNr_integrable (g : WeilCompactSmoothGV1) (c : ℝ) :
    Integrable (fun t => Real.cos (t * c) * Nr g t) := by
  refine (Nr_integrable g).bdd_mul (c := 1) ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _

theorem arch_even (g : WeilCompactSmoothGV1) :
    (∫ t : ℝ, (Psi t - Real.log Real.pi) * ((Nr g t + Nr g (-t)) / 2)) =
      ∫ t : ℝ, (Psi t - Real.log Real.pi) * Nr g t := by
  have h1 : Integrable (fun t => (Psi t - Real.log Real.pi) * Nr g t) := by
    have := (psiNr_integrable g).sub ((Nr_integrable g).const_mul (Real.eulerMascheroniConstant + Real.log Real.pi))
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]; ring
  have h2 : Integrable (fun t => (Psi t - Real.log Real.pi) * Nr g (-t)) := by
    refine h1.comp_neg.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Psi_even]
  have hsplit : ∀ t, (Psi t - Real.log Real.pi) * ((Nr g t + Nr g (-t)) / 2) =
      (1 / 2) * ((Psi t - Real.log Real.pi) * Nr g t) +
        (1 / 2) * ((Psi t - Real.log Real.pi) * Nr g (-t)) := fun t => by ring
  simp_rw [hsplit]
  rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
  have hneg : (∫ t : ℝ, (Psi t - Real.log Real.pi) * Nr g (-t)) =
      ∫ t : ℝ, (Psi t - Real.log Real.pi) * Nr g t := by
    rw [← integral_neg_eq_self (fun t => (Psi t - Real.log Real.pi) * Nr g t)]
    congr 1; funext t; rw [Psi_even]
  rw [hneg]; ring

/-- The certificate symbol: `Re ψ(1/4+it/2) − log π − log 2·(2·2^{-1/2})·cos(t log 2)`
(the prime-power sum truncated to `m = 2`). -/
def Scert (t : ℝ) : ℝ :=
  Psi t - Real.log Real.pi -
    Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)) * Real.cos (t * Real.log 2)

theorem prime_int (g : WeilCompactSmoothGV1) (K c : ℝ) :
    (∫ t : ℝ, ((K * Real.cos (t * c) : ℝ) : ℂ) * criticalDensityV1 g t) =
      (((K * ∫ t : ℝ, Real.cos (t * c) * Nr g t) : ℝ) : ℂ) := by
  simp_rw [criticalDensity_eq, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, ← integral_const_mul]
  congr 2; funext t; ring

/-- **The zero quadratic as a single symbol integral** on log-support width `2r < log 3`. -/
theorem zero_quadratic_eq_scert (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (hr3 : 2 * r < Real.log 3) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, Scert t * Nr g t := by
  rw [zero_quadratic_krein_form_v1 g hm]
  have hts : ∀ n : ℕ, n ≠ 1 →
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, ((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
              Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * criticalDensityV1 g t) = 0 := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 0 := by omega
      subst this; simp
    · rw [prime_int, cos_pair_zero g r a hw]
      · simp
      · have h3 : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          have : (3 : ℕ) ≤ n + 1 := by omega
          exact_mod_cast this
        have := Real.log_le_log (by norm_num) h3
        linarith
  have hae := arch_even g
  simp only [Psi] at hae
  rw [tsum_eq_single 1 hts, prime_int, hae]
  have hΛ : (ArithmeticFunction.vonMangoldt (1 + 1) : ℝ) = Real.log 2 := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have h2 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [hΛ, h2]
  have hA : Integrable (fun t => (Psi t - Real.log Real.pi) * Nr g t) := by
    have := (psiNr_integrable g).sub
      ((Nr_integrable g).const_mul (Real.eulerMascheroniConstant + Real.log Real.pi))
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]; ring
  have hB := (cosNr_integrable g (Real.log 2)).const_mul
    (Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)))
  have hS : (∫ t : ℝ, Scert t * Nr g t) =
      (∫ t : ℝ, (Psi t - Real.log Real.pi) * Nr g t) -
        Real.log 2 * ((2 * Real.exp (-(Real.log 2) / 2)) *
          ∫ t : ℝ, Real.cos (t * Real.log 2) * Nr g t) := by
    rw [← mul_assoc, ← integral_const_mul, ← integral_sub hA hB]
    congr 1; funext t; simp only [Scert, Psi]; ring
  have hc : ∀ X Y : ℝ, ((1 / (2 * (Real.pi : ℂ))) * (X : ℂ) -
      ((Real.log 2 : ℝ) : ℂ) * ((1 / (2 * (Real.pi : ℂ))) * (Y : ℂ))) =
      (((1 / (2 * Real.pi)) * X - Real.log 2 * ((1 / (2 * Real.pi)) * Y) : ℝ) : ℂ) := by
    intro X Y; push_cast; ring
  rw [hc, Complex.ofReal_re, hS]
  simp only [Psi]
  ring

theorem scertNr_integrable (g : WeilCompactSmoothGV1) :
    Integrable (fun t => Scert t * Nr g t) := by
  have hA := (psiNr_integrable g).sub
    ((Nr_integrable g).const_mul (Real.eulerMascheroniConstant + Real.log Real.pi))
  have hB := (cosNr_integrable g (Real.log 2)).const_mul
    (Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)))
  refine (hA.sub hB).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, Scert]; ring

theorem integral_two_pi (f : ℝ → ℝ) :
    (∫ ν : ℝ, f (2 * Real.pi * ν)) = (1 / (2 * Real.pi)) * ∫ t : ℝ, f t := by
  rw [MeasureTheory.Measure.integral_comp_mul_left, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (by positivity)), one_div]

/-- **Krein certificate ⇒ lower bound on the zeta zero quadratic.** If the pointwise certificate
inequality holds for window `L ≤ log 3`, then every moment-zero packet of log-support width `2r < L`
satisfies `Re Σ_ρ Z_ρ(A_g) ≥ (m/2π) ∫ Nr`. -/
theorem certificate_zero_quadratic_lower (L m : ℝ) (hL3 : L ≤ Real.log 3)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (Scert t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < L) (hw : HalfWidthAt g r a) :
    m * ((1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t) ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  obtain ⟨chi, hc, hs, hNr⟩ := Nr_factor g r a hr hw hmom
  set ε := (L - 2 * r) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hts : tsupport chi ⊆ Set.Ioo (-a - r - ε) (-a + r + ε) :=
    hs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hba : (-a + r + ε) - (-a - r - ε) = L := by rw [hε]; ring
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hNrν : ∀ ν : ℝ, Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν) = Nr g (2 * Real.pi * ν) := by
    intro ν; rw [hNr, two_pi_div]
  have hW : Integrable (fun ν => Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) := by
    refine ((Nr_integrable g).comp_mul_left' h2pi).congr
      (Filter.Eventually.of_forall fun ν => ?_)
    simp only [hNrν]
  have hWS : Integrable (fun ν => Wt (2 * Real.pi * ν) * Scert (2 * Real.pi * ν) *
      Complex.normSq (𝓕 chi ν)) := by
    refine ((scertNr_integrable g).comp_mul_left' h2pi).congr
      (Filter.Eventually.of_forall fun ν => ?_)
    show Scert (2 * Real.pi * ν) * Nr g (2 * Real.pi * ν) = _
    rw [← hNrν]; ring
  have hcert' : ∀ ξ : ℝ, 0 ≤ Wt (2 * Real.pi * ξ) * (Scert (2 * Real.pi * ξ) - m) +
      (∑ i, 𝓕 (H i) ξ).re + ∑ l, 2 * (d l * ((2 * Real.pi * I * ξ) ^ j l *
        Complex.exp (↑(2 * Real.pi * ξ * L) * I))).re := by
    intro ξ
    have h := hcert (2 * Real.pi * ξ)
    rw [two_pi_div] at h
    have e1 : ∀ l, (I * (((2 * Real.pi * ξ : ℝ)) : ℂ)) ^ j l = (2 * (Real.pi : ℂ) * I * ξ) ^ j l := by
      intro l; push_cast; ring_nf
    simp only [e1] at h
    exact h
  have hHs' : ∀ i u, |u| < (-a + r + ε) - (-a - r - ε) → H i u = 0 := by
    rw [hba]; exact hHs
  have key := AEGIS.RHKreinCertificateV1.certificate_lower_bound chi hc _ _ hts L hba.le
    (fun ν => Wt (2 * Real.pi * ν)) (fun ν => Scert (2 * Real.pi * ν)) m H hHc hHi hFH hHs' d j
    hWS hW hcert'
  have e2 : (∫ ν, Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) =
      (1 / (2 * Real.pi)) * ∫ t, Nr g t := by
    rw [← integral_two_pi (Nr g)]; congr 1; funext ν; exact hNrν ν
  have e3 : (∫ ν, Wt (2 * Real.pi * ν) * Scert (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) =
      (1 / (2 * Real.pi)) * ∫ t, Scert t * Nr g t := by
    rw [← integral_two_pi (fun t => Scert t * Nr g t)]; congr 1; funext ν
    show _ = Scert (2 * Real.pi * ν) * Nr g (2 * Real.pi * ν)
    rw [← hNrν]; ring
  rw [e2, e3] at key
  rw [zero_quadratic_eq_scert g hmom r a hw (by linarith)]
  exact key

/-- **Corollary.** With `m ≥ 0`: the zeta zero quadratic is nonnegative on the width-`< L` class. -/
theorem certificate_zero_quadratic_nonneg (L m : ℝ) (hm0 : 0 ≤ m) (hL3 : L ≤ Real.log 3)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (Scert t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < L) (hw : HalfWidthAt g r a) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have h := certificate_zero_quadratic_lower L m hL3 H hHc hHi hFH hHs d j hcert g hmom r a hr hrL hw
  have hN : 0 ≤ ∫ t : ℝ, Nr g t := integral_nonneg (Nr_nonneg g)
  have : 0 ≤ m * ((1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t) := by positivity
  linarith

end AEGIS.RHKreinZetaBridgeV1

#print axioms AEGIS.RHKreinZetaBridgeV1.zero_quadratic_eq_scert
#print axioms AEGIS.RHKreinZetaBridgeV1.certificate_zero_quadratic_lower
#print axioms AEGIS.RHKreinZetaBridgeV1.certificate_zero_quadratic_nonneg
