import WeilCriticalLineBridgeV1
import WeilFixedLineCompletedGammaV10
import WeilDigammaSeriesHalfPlaneV1
import Mathlib.Tactic

/-!
AEGIS Ω — the repository zero quadratic in Krein form.

For moment-zero compact-smooth g let N(t) = |Mg(1/2+it)|² and
E(t) = (N(t) + N(-t))/2 (its even part).  Then

  Σ_ρ Z_ρ(A_g) = (1/2π) ∫ (Re ψ(1/4 + it/2) − log π) · E(t) dt
                 − Σ_m Λ(m) (1/2π) ∫ 2 m^{-1/2} cos(t log m) N(t) dt,

i.e. the Krein t-form with symbol Re ψ(1/4+it/2) − log π − Σ Λ(m) 2 m^{-1/2} cos(t log m).
Identity only: no sign, positivity, or RH claim.  AUTHORITY_EFFECT = NONE.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilCriticalLineKreinFormV1

open AEGIS.WeilDigammaIntegralReductionV1
open AEGIS.WeilDigammaSeriesHalfPlaneV1
open AEGIS.WeilCriticalLineArchV1
open AEGIS.WeilCriticalLinePrimeV1
open AEGIS.WeilCriticalLineBridgeV1
open AEGIS.WeilFixedLineCompletedGammaV10

theorem digamma_conj_v1 (z : ℂ) (hz : 0 < z.re) :
    Complex.digamma (conj z) = conj (Complex.digamma z) := by
  have hz' : 0 < (conj z).re := by simpa using hz
  have h1 := digamma_series_halfPlane_v1 z hz
  have h2 := digamma_series_halfPlane_v1 (conj z) hz'
  have hterm : ∀ n : ℕ, conj (seriesTerm z n) = seriesTerm (conj z) n := by
    intro n
    simp [seriesTerm, map_sub]
  have h3 : conj (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)) =
      Complex.digamma (conj z) + (Real.eulerMascheroniConstant : ℂ) := by
    rw [h1, h2, Complex.conj_tsum]
    exact tsum_congr hterm
  rw [map_add, Complex.conj_ofReal] at h3
  linear_combination -h3

/-- The critical-line digamma argument (1/2 + it)/2. -/
def zt (t : ℝ) : ℂ := (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2

theorem zt_re (t : ℝ) : 0 < (zt t).re := by
  simp [zt]

theorem conj_zt (t : ℝ) : conj (zt t) = zt (-t) := by
  unfold zt
  rw [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast
  ring

/-- Real critical density. -/
def Nr (g : WeilCompactSmoothGV1) (t : ℝ) : ℝ :=
  Complex.normSq (mellin g.1 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))

theorem criticalDensity_eq (g : WeilCompactSmoothGV1) (t : ℝ) :
    criticalDensityV1 g t = ((Nr g t : ℝ) : ℂ) := rfl

/-- The Archimedean integrand of the bridge. -/
def archF (g : WeilCompactSmoothGV1) (t : ℝ) : ℂ :=
  (Complex.digamma (zt t) + (Real.eulerMascheroniConstant : ℂ)) *
    (criticalDensityV1 g t + criticalDensityV1 g (-t))

theorem archF_integrable (g : WeilCompactSmoothGV1) : Integrable (archF g) := by
  have h := digamma_plus_gamma_profile_integrable_v10
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [archF, zt]
  rw [profile_critical_v1]

theorem conj_archF (g : WeilCompactSmoothGV1) (t : ℝ) :
    conj (archF g t) = archF g (-t) := by
  simp only [archF, criticalDensity_eq, map_mul, map_add, Complex.conj_ofReal, neg_neg]
  rw [← digamma_conj_v1 _ (zt_re t), conj_zt]
  ring

theorem archF_integral_real (g : WeilCompactSmoothGV1) :
    (∫ t : ℝ, archF g t) = (((∫ t : ℝ, (archF g t).re) : ℝ) : ℂ) := by
  have hc : conj (∫ t : ℝ, archF g t) = ∫ t : ℝ, archF g t := by
    rw [← integral_conj]
    simp_rw [conj_archF]
    exact integral_neg_eq_self (fun t => archF g t) volume
  have hre := integral_re (archF_integrable g)
  rw [Complex.conj_eq_iff_re] at hc
  rw [← hc]
  congr 1
  exact hre.symm

theorem archF_re (g : WeilCompactSmoothGV1) (t : ℝ) :
    (archF g t).re =
      ((Complex.digamma (zt t)).re + Real.eulerMascheroniConstant) * (Nr g t + Nr g (-t)) := by
  simp [archF, criticalDensity_eq, Complex.mul_re]


theorem Nr_integrable (g : WeilCompactSmoothGV1) : Integrable (Nr g) := by
  have h := (criticalDensity_integrable_v1 g).re
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp [criticalDensity_eq]

theorem log_four_pi_v1 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- Real form of the Archimedean + constant part. -/
theorem arch_constant_real_v1 (g : WeilCompactSmoothGV1) :
    (1 / 2 : ℝ) * (∫ t : ℝ, (archF g t).re) -
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant - 2 * Real.log 2) *
          (∫ t : ℝ, Nr g t) =
      ∫ t : ℝ, ((Complex.digamma (zt t)).re - Real.log Real.pi) *
        ((Nr g t + Nr g (-t)) / 2) := by
  set γ := Real.eulerMascheroniConstant
  have hNr := Nr_integrable g
  have hNrn : Integrable (fun t => Nr g (-t)) := hNr.comp_neg
  have hA : Integrable (fun t => Nr g t + Nr g (-t)) := hNr.add hNrn
  have hRe : Integrable (fun t => (archF g t).re) := (archF_integrable g).re
  have hpt : ∀ t : ℝ, ((Complex.digamma (zt t)).re - Real.log Real.pi) *
        ((Nr g t + Nr g (-t)) / 2) =
      (1 / 2 : ℝ) * (archF g t).re - ((Real.log Real.pi + γ) / 2) * (Nr g t + Nr g (-t)) := by
    intro t; rw [archF_re]; ring
  simp_rw [hpt]
  rw [integral_sub (hRe.const_mul _) (hA.const_mul _), integral_const_mul, integral_const_mul,
    integral_add hNr hNrn, integral_neg_eq_self (fun t => Nr g t) volume, log_four_pi_v1]
  ring

/-- **Krein form of the repository zero quadratic.** -/
theorem zero_quadratic_krein_form_v1
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho) =
      (1 / (2 * Real.pi) : ℂ) *
          (((∫ t : ℝ, ((Complex.digamma (zt t)).re - Real.log Real.pi) *
              ((Nr g t + Nr g (-t)) / 2)) : ℝ) : ℂ)
      - ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
            ((1 / (2 * Real.pi) : ℂ) *
              ∫ t : ℝ, ((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
                  Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
                criticalDensityV1 g t) := by
  rw [zero_quadratic_critical_line_v1 g hm]
  have hI : (∫ t : ℝ,
      (Complex.digamma (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)) +
          (Real.eulerMascheroniConstant : ℂ)) *
        (criticalDensityV1 g t + criticalDensityV1 g (-t))) = ∫ t : ℝ, archF g t := rfl
  have hN : (∫ t : ℝ, criticalDensityV1 g t) = (((∫ t : ℝ, Nr g t) : ℝ) : ℂ) := by
    simp_rw [criticalDensity_eq]
    exact integral_ofReal
  rw [hI, archF_integral_real, hN, ← arch_constant_real_v1 g]
  push_cast
  ring

end AEGIS.WeilCriticalLineKreinFormV1

#print axioms AEGIS.WeilCriticalLineKreinFormV1.archF_integral_real
#print axioms AEGIS.WeilCriticalLineKreinFormV1.zero_quadratic_krein_form_v1
