import WeilFixedLineGammaXSpaceV10
import WeilAutocorrelationMellinV11
import Mathlib.Tactic

/-!
AEGIS Ω — the Archimedean term on the critical line (c = 1/2).

With the V10 Gauss-kernel chain valid for every c > 0, its x-space identity
specializes to the line Re s = 1/2, where the digamma argument is
(1/2 + i t)/2 = 1/4 + i t/2.  For an autocorrelation packet the V11 Mellin
factorization turns the paired profile on that line into |Mg(1/2+it)|² +
|Mg(1/2-it)|².  Together these are the Archimedean half of the bridge from the
repository zero quadratic to the Krein t-form (1/2π) ∫ |ĝ|² · S.

No sign, positivity, or RH claim is made.  AUTHORITY_EFFECT = NONE.
-/

open Complex
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilCriticalLineArchV1

open AEGIS.WeilFixedLineGammaXSpaceV10
open AEGIS.WeilAutocorrelationMellinV11

/-- The Archimedean x-space term as a t-integral on the critical line. -/
theorem critical_line_arch_v1 (f : WeilCompactSmoothGV1) :
    (1 / 2 : ℂ) *
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (Complex.digamma
            (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)) +
              (Real.eulerMascheroniConstant : ℂ)) *
            WeilPairedMellinProfileV5 f (1 / 2) t) =
      -WeilArchimedeanIntegralV1 f.1 -
        ((2 * Real.log 2 : ℝ) : ℂ) * f.1 1 :=
  half_fixed_line_digamma_plus_gamma_eq_arch_v10 f (1 / 2) (by norm_num)

/-- On the critical line the paired profile of an autocorrelation packet is a
sum of two squared Mellin moduli. -/
theorem critical_line_profile_autocorrelation_v1
    (g : WeilCompactSmoothGV1) (t : ℝ) :
    WeilPairedMellinProfileV5 (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) t =
      (Complex.normSq (mellin g.1 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) : ℂ) +
        (Complex.normSq (mellin g.1 (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) : ℂ) := by
  unfold WeilPairedMellinProfileV5
  have e1 : (1 : ℂ) - conj (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> norm_num
  have e2 : (1 : ℂ) - conj ((((1 - 1 / 2 : ℝ)) : ℂ) + ((-t : ℝ) : ℂ) * I) =
      ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> norm_num
  have h1 := weil_autocorrelation_mellin_factorization_v11 g
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have h2 := weil_autocorrelation_mellin_factorization_v11 g
    ((((1 - 1 / 2 : ℝ)) : ℂ) + ((-t : ℝ) : ℂ) * I)
  rw [e1] at h1
  rw [e2] at h2
  have hhalf : ((1 - 1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf] at h2
  change mellin (WeilAutocorrelationV1 g) _ + mellin (WeilAutocorrelationV1 g) _ = _
  rw [hhalf, h1, h2, Complex.mul_conj, Complex.mul_conj]

end AEGIS.WeilCriticalLineArchV1

#print axioms AEGIS.WeilCriticalLineArchV1.critical_line_arch_v1
#print axioms AEGIS.WeilCriticalLineArchV1.critical_line_profile_autocorrelation_v1
