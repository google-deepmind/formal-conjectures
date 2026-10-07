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


import WeilAutocorrelationMellinFactorV10
import WeilAutocorrelationExplicitFormulaV10
import WeilZeroSideIdentificationV1
import Mathlib.Tactic

/-!
AEGIS Ω — RH implies the final Weil sign residual, V11.

This compatibility form removes a redundant Fourier/convolution detour and
uses the already-kernel-checked exact Mellin autocorrelation factorization

  M(A_g)(s) = M(g)(s) * conj(M(g)(1 - conj s)).

On the critical line s = 1/2 + iγ, the reflected point equals s, so the
autocorrelation Mellin value is exactly the real nonnegative norm square.
Under Mathlib's RiemannHypothesis, every canonical nontrivial zeta zero lies
on that line. Hence every multiplicity-weighted zero summand has nonnegative
real part, and summability upgrades pointwise nonnegativity to the full zero
quadratic. The existing explicit-formula bridge then yields the repository
FinalSignResidualV1.

AUTHORITY_EFFECT = NONE.
The reverse implication is not asserted in this file.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilRHImpliesFinalSignV11

open AEGIS.WeilAutocorrelationMellinFactorV10
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- On the critical line, the exact autocorrelation Mellin factorization is a
norm square. -/
theorem autocorrelation_mellin_critical_normSq_v11
    (g : WeilCompactSmoothGV1) (γ : ℝ) :
    mellin (WeilAutocorrelationV1 g)
        (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) =
      (Complex.normSq
        (mellin g.1 (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I)) : ℂ) := by
  rw [mellin_autocorrelation_factor_v10]
  have hreflect :
      1 - conj ((((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I)) =
        (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) := by
    apply Complex.ext <;> simp <;> ring
  rw [hreflect]
  exact Complex.mul_conj _

/-- Under RH, every canonical zero summand of the autocorrelation has
nonnegative real part. -/
theorem rh_zero_summand_nonnegative_v11
    (hRH : RiemannHypothesis)
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    0 ≤ (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hrho1 : rho.1 ≠ 1 := by
    intro h
    rw [h] at hstrip
    norm_num at hstrip
  have hcrit :
      rho.1.re = 1 / 2 :=
    hRH rho.1 rho.2.1 rho.2.2 hrho1
  have hrho :
      rho.1 =
        (((1 / 2 : ℝ) : ℂ) + (rho.1.im : ℂ) * I) := by
    apply Complex.ext
    · simpa [hcrit]
    · simp
  have hM :
      mellin (WeilAutocorrelationV1 g) rho.1 =
        (Complex.normSq (mellin g.1 rho.1) : ℂ) := by
    rw [hrho]
    exact autocorrelation_mellin_critical_normSq_v11 g rho.1.im
  unfold WeilZeroIndexSummandV1
  rw [hM]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- RH makes the full canonical autocorrelation zero quadratic nonnegative. -/
theorem rh_zero_quadratic_nonnegative_v11
    (hRH : RiemannHypothesis)
    (g : WeilCompactSmoothGV1) :
    0 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hsum :=
    weil_compact_smooth_zero_summable_v1
      (WeilAutocorrelationCompactSmoothV1 g)
  change
    Summable
      (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g)) at hsum
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg (fun rho =>
    rh_zero_summand_nonnegative_v11 hRH g rho)

/-- Mathlib RH implies the repository final sign residual. -/
theorem rh_implies_final_sign_residual_v11
    (hRH : RiemannHypothesis) :
    AEGIS.RHFinalClosureV1.FinalSignResidualV1 := by
  rw [final_sign_residual_iff_zero_quadratic_nonnegative_v10]
  intro g _
  exact rh_zero_quadratic_nonnegative_v11 hRH g

end AEGIS.WeilRHImpliesFinalSignV11

#print axioms AEGIS.WeilRHImpliesFinalSignV11.autocorrelation_mellin_critical_normSq_v11
#print axioms AEGIS.WeilRHImpliesFinalSignV11.rh_zero_summand_nonnegative_v11
#print axioms AEGIS.WeilRHImpliesFinalSignV11.rh_zero_quadratic_nonnegative_v11
#print axioms AEGIS.WeilRHImpliesFinalSignV11.rh_implies_final_sign_residual_v11
