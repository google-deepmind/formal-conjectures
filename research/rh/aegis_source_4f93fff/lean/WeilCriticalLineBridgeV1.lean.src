import WeilCriticalLineArchV1
import WeilCriticalLinePrimeV1
import WeilAutocorrelationExplicitFormulaV10
import Mathlib.Tactic

/-!
AEGIS Ω — the repository zero quadratic as a critical-line t-integral.

For a moment-zero compact-smooth g with critical density
N(t) = |Mg(1/2+it)|², the canonical zero quadratic of its autocorrelation is

  Σ_ρ Z_ρ = (1/2)(1/2π) ∫ (ψ((1/2+it)/2) + γ)(N(t) + N(-t)) dt
            - (log 4π + γ - 2 log 2)·(1/2π) ∫ N
            - Σ_{m≥2} Λ(m)·(1/2π) ∫ 2 m^{-1/2} cos(t log m) N(t) dt.

This is the bridge RH_STATUS lists as missing between the repository zero
quadratic and the Krein t-form (1/2π) ∫ |ĝ|² S.  It is an identity only:
no sign, positivity, or RH claim is made.  AUTHORITY_EFFECT = NONE.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilCriticalLineBridgeV1

open AEGIS.WeilCriticalLineArchV1
open AEGIS.WeilCriticalLinePrimeV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10

theorem autocorrelation_one_critical_v1 (g : WeilCompactSmoothGV1) :
    WeilAutocorrelationV1 g 1 =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, criticalDensityV1 g t := by
  rw [autocorrelation_critical_line_inversion_v1 g one_pos]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [criticalDensityV1]

theorem prime_term_critical_v1 (g : WeilCompactSmoothGV1) (n : ℕ) :
    WeilPrimeTermV1 (WeilAutocorrelationV1 g) n =
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, ((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
              Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
            criticalDensityV1 g t) := by
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [← prime_pair_critical_cos_v1 g hm]
  unfold WeilPrimeTermV1
  push_cast
  ring_nf

theorem profile_critical_v1 (g : WeilCompactSmoothGV1) (t : ℝ) :
    WeilPairedMellinProfileV5 (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) t =
      criticalDensityV1 g t + criticalDensityV1 g (-t) := by
  rw [critical_line_profile_autocorrelation_v1]
  rfl

/-- **Critical-line bridge.** -/
theorem zero_quadratic_critical_line_v1
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho) =
      (1 / 2 : ℂ) * ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (Complex.digamma (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)) +
              (Real.eulerMascheroniConstant : ℂ)) *
            (criticalDensityV1 g t + criticalDensityV1 g (-t)))
      - (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant - 2 * Real.log 2 : ℝ)) : ℂ) *
          ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, criticalDensityV1 g t)
      - ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
            ((1 / (2 * Real.pi) : ℂ) *
              ∫ t : ℝ, ((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
                  Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
                criticalDensityV1 g t) := by
  have hEF := autocorrelation_explicit_formula_v10 g hm
  have hZ : (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho) =
      -WeilExplicitRightSideV1 (WeilAutocorrelationV1 g) := by
    rw [hEF]; ring
  rw [hZ]
  have harch := critical_line_arch_v1 (WeilAutocorrelationCompactSmoothV1 g)
  have hprof : (fun t : ℝ =>
      (Complex.digamma (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)) +
          (Real.eulerMascheroniConstant : ℂ)) *
        WeilPairedMellinProfileV5 (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) t) =
      (fun t : ℝ =>
      (Complex.digamma (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)) +
          (Real.eulerMascheroniConstant : ℂ)) *
        (criticalDensityV1 g t + criticalDensityV1 g (-t))) := by
    funext t
    rw [profile_critical_v1]
  rw [hprof] at harch
  change _ = -WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g) -
    ((2 * Real.log 2 : ℝ) : ℂ) * WeilAutocorrelationV1 g 1 at harch
  unfold WeilExplicitRightSideV1 WeilPrimeSumV1 WeilArchimedeanConstantV1
  have hprime : (∑' n : ℕ, WeilPrimeTermV1 (WeilAutocorrelationV1 g) n) =
      ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
            ((1 / (2 * Real.pi) : ℂ) *
              ∫ t : ℝ, ((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
                  Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
                criticalDensityV1 g t) :=
    tsum_congr fun n => prime_term_critical_v1 g n
  rw [hprime, ← autocorrelation_one_critical_v1 g]
  push_cast at harch ⊢
  linear_combination -harch

end AEGIS.WeilCriticalLineBridgeV1

#print axioms AEGIS.WeilCriticalLineBridgeV1.autocorrelation_one_critical_v1
#print axioms AEGIS.WeilCriticalLineBridgeV1.prime_term_critical_v1
#print axioms AEGIS.WeilCriticalLineBridgeV1.zero_quadratic_critical_line_v1
