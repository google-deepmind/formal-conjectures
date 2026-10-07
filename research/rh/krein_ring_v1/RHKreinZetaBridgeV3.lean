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

import RHKreinZetaBridgeV2

/-!
# Krein bridge with all prime powers below `M + 1` (v3)

`ScertM M t = Re ψ(1/4+it/2) − log π − Σ_{n<M} Λ(n+1)·2(n+1)^{-1/2} cos(t log(n+1))`.
For log-support width `2r < log (M+1)` every prime power `≥ M+1` pairs to zero, so the zero quadratic
is `(1/2π)∫ ScertM·Nr` (`zero_quadratic_eq_scertM`), and a certificate with symbol `ScertM` on a window
`L ≤ log (M+1)` gives `Re Σ_ρ Z_ρ ≥ 0` on width `< L` (`certificateM_zero_quadratic_nonneg`).
V1 is `M = 2`, V2 is `M = 3`.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinZetaBridgeV3

open AEGIS.WeilCriticalLineKreinFormV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilCriticalLinePrimeV1
open AEGIS.RHKreinZetaBridgeV1
open AEGIS.RHKreinZetaBridgeV2

/-- Prime-power weight of `n + 1`: `Λ(n+1) · 2 (n+1)^{-1/2}`. -/
def ppw (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * (2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2))

def ScertM (M : ℕ) (t : ℝ) : ℝ :=
  Psi t - Real.log Real.pi - ∑ n ∈ Finset.range M, ppw n * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))

theorem psiLogNr_integrable (g : WeilCompactSmoothGV1) :
    Integrable (fun t => (Psi t - Real.log Real.pi) * Nr g t) := by
  have := (psiNr_integrable g).sub
    ((Nr_integrable g).const_mul (Real.eulerMascheroniConstant + Real.log Real.pi))
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]; ring

theorem primeSum_integrable (M : ℕ) (g : WeilCompactSmoothGV1) :
    Integrable (fun t => ∑ n ∈ Finset.range M,
      ppw n * (Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) * Nr g t)) :=
  integrable_finsetSum _ fun n _ => (cosNr_integrable g _).const_mul _

theorem scertMNr_integrable (M : ℕ) (g : WeilCompactSmoothGV1) :
    Integrable (fun t => ScertM M t * Nr g t) := by
  refine ((psiLogNr_integrable g).sub (primeSum_integrable M g)).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, ScertM, sub_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl; intro n _; ring

theorem integral_scertM (M : ℕ) (g : WeilCompactSmoothGV1) :
    (∫ t : ℝ, ScertM M t * Nr g t) =
      (∫ t : ℝ, (Psi t - Real.log Real.pi) * Nr g t) -
        ∑ n ∈ Finset.range M, ppw n * ∫ t : ℝ, Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) * Nr g t := by
  have h : (fun t => ScertM M t * Nr g t) = fun t => (Psi t - Real.log Real.pi) * Nr g t -
      ∑ n ∈ Finset.range M, ppw n * (Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) * Nr g t) := by
    funext t
    simp only [ScertM, Finset.sum_mul, sub_mul]
    congr 1
    apply Finset.sum_congr rfl; intro n _; ring
  rw [h, integral_sub (psiLogNr_integrable g) (primeSum_integrable M g),
    integral_finsetSum _ fun n _ => (cosNr_integrable g _).const_mul _]
  congr 1
  apply Finset.sum_congr rfl; intro n _
  rw [integral_const_mul]

theorem zero_quadratic_eq_scertM (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (M : ℕ) (hM : 2 * r < Real.log ((M + 1 : ℕ) : ℝ)) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ScertM M t * Nr g t := by
  rw [zero_quadratic_krein_form_v1 g hm]
  have hts : ∀ n : ℕ, n ∉ Finset.range M →
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, ((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
              Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * criticalDensityV1 g t) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [prime_int, cos_pair_zero g r a hw]
    · simp
    · have hle : ((M + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hn
      have hpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
      have := Real.log_le_log hpos hle
      linarith
  have hae := arch_even g
  simp only [Psi] at hae
  rw [tsum_eq_sum hts]
  simp_rw [prime_int]
  rw [hae]
  have key : (1 / (2 * Real.pi) : ℂ) *
        (((∫ t : ℝ, ((Complex.digamma (zt t)).re - Real.log Real.pi) * Nr g t) : ℝ) : ℂ) -
      ∑ n ∈ Finset.range M, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) *
          (((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
            ∫ t : ℝ, Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) * Nr g t) : ℝ) : ℂ)) =
      (((1 / (2 * Real.pi)) * ((∫ t : ℝ, (Psi t - Real.log Real.pi) * Nr g t) -
        ∑ n ∈ Finset.range M, ppw n *
          ∫ t : ℝ, Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) * Nr g t) : ℝ) : ℂ) := by
    push_cast
    simp only [Psi, ppw]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro n _
    push_cast; ring
  rw [key, Complex.ofReal_re, integral_scertM]

/-- **Certificate with all prime powers `≤ M` ⇒ nonnegative zeta zero quadratic on width `< L`,
`L ≤ log (M+1)`.** -/
theorem certificateM_zero_quadratic_nonneg (M : ℕ) (L m : ℝ) (hm0 : 0 ≤ m)
    (hLM : L ≤ Real.log ((M + 1 : ℕ) : ℝ))
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < L) (hw : HalfWidthAt g r a) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have h := certificate_generic (ScertM M) L m H hHc hHi hFH hHs d j hcert g hmom r a hr hrL hw
    (scertMNr_integrable M g) (zero_quadratic_eq_scertM g hmom r a hw M (by linarith))
  have hN : 0 ≤ ∫ t : ℝ, Nr g t := integral_nonneg (Nr_nonneg g)
  have : 0 ≤ m * ((1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t) := by positivity
  linarith

end AEGIS.RHKreinZetaBridgeV3

#print axioms AEGIS.RHKreinZetaBridgeV3.zero_quadratic_eq_scertM
#print axioms AEGIS.RHKreinZetaBridgeV3.certificateM_zero_quadratic_nonneg
