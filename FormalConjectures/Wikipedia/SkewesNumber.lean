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
module

public import FormalConjecturesUtil

/-!
# Skewes's Number and Sign Changes of $\pi(x) - \operatorname{li}(x)$

Let $\pi(x)$ count primes up to $x$ and let
$\operatorname{li}(x) = \operatorname{pv} \int_0^x \frac{dt}{\log t}$ denote the Cauchy
principal-value logarithmic integral. John Edensor Littlewood (1914) proved that
$\pi(x) - \operatorname{li}(x)$ reverses sign infinitely often, and Stanley Skewes (1933, 1955)
established the first explicit upper bounds for a crossover point. Analytic zero-free and
explicit-formula bounds show $\pi(x) < \operatorname{li}(x)$ for $2 \le x \le 10^{19}$ (Büthe
2015), while a crossing region is unconditionally bracketed near $e^{727.95133} \approx
1.3972 \times 10^{316}$ (Bays–Hudson 2000; Saouter–Demichel 2010; Saouter–Trudgian–Demichel 2015).
Determining the least integer $n \ge 2$ with $\pi(n) > \operatorname{li}(n)$—and whether any
crossing precedes the $e^{727.95133}$ region—remains open.

*References:*
- [Wikipedia: Skewes's number](https://en.wikipedia.org/wiki/Skewes%27s_number)
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- J. E. Littlewood, *Sur la distribution des nombres premiers*, C. R. Acad. Sci. **158**
  (1914), 1869–1872.
- S. Skewes, *On the difference $\pi(x) - \operatorname{li}(x)$*, J. London Math. Soc. **8**
  (1933), 277–283.
- S. Skewes, *On the difference $\pi(x) - \operatorname{li}(x)$ (II)*, Proc. London Math. Soc. (3)
  **5** (1955), 48–70.
- C. Bays and R. H. Hudson, *A new bound for the smallest $x$ with $\pi(x) > \operatorname{li}(x)$*,
  Math. Comp. **69** (2000), no. 231, 1285–1296.
- Y. Saouter, T. Trudgian, and P. Demichel, *A still sharper region where
  $\pi(x) - \operatorname{li}(x)$ is positive*, Math. Comp. **84** (2015), no. 295, 2433–2446.
- J. Büthe, *An analytic method for bounding $\psi(x)$*, Math. Comp. **87** (2018), no. 312,
  1991–2009 (`arXiv:1511.02032`, 2015).
-/

@[expose] public section

namespace SkewesNumber

/-- Cauchy principal value
$\operatorname{li}(2) = \int_0^1 \left(\frac{1}{\log(1 + u)} + \frac{1}{\log(1 - u)}\right) du
\approx 1.04516378$. -/
noncomputable def logIntegralTwo : ℝ :=
  ∫ u in Set.Ioo (0 : ℝ) 1, (1 / Real.log (1 + u) + 1 / Real.log (1 - u))

/-- Principal-value logarithmic integral
$\operatorname{li}(x) = \operatorname{li}(2) + \int_2^x \frac{dt}{\log t}$ for $x > 1$ (evaluated
at integers $n \ge 2$ below; for $x \le 1$, the non-integrable interval integral across $t = 1$
vanishes in Mathlib). -/
noncomputable def logIntegral (x : ℝ) : ℝ :=
  logIntegralTwo + ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- On $(0, 1)$, the symmetrized Cauchy principal-value integrand defining `logIntegralTwo` is
strictly positive. -/
@[category API, AMS 11]
theorem logIntegralTwo_integrand_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < 1 / Real.log (1 + u) + 1 / Real.log (1 - u) := by
  have hpos : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
  have hneg : Real.log (1 - u) < 0 := Real.log_neg (by linarith) (by linarith)
  have hsum : Real.log (1 - u) + Real.log (1 + u) < 0 := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_neg (by nlinarith) (by nlinarith)
  rw [div_add_div _ _ hpos.ne' hneg.ne]
  exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg hpos hneg)

/-- On $(0, 1)$, the symmetrized Cauchy principal-value integrand defining `logIntegralTwo` is
bounded above by $2$. -/
@[category API, AMS 11]
theorem logIntegralTwo_integrand_le_two {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 / Real.log (1 + u) + 1 / Real.log (1 - u) ≤ 2 := by
  have h1pu : 0 < 1 + u := by linarith
  have h1mu : 0 < 1 - u := by linarith
  have hpos : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
  have hneg : 0 < -Real.log (1 - u) := neg_pos.mpr (Real.log_neg h1mu (by linarith))
  have hb1 : 1 / Real.log (1 + u) ≤ (1 + u) / u := by
    rw [div_le_div_iff₀ hpos hu0]
    have := mul_le_mul_of_nonneg_right (Real.one_sub_inv_le_log_of_pos h1pu) h1pu.le
    have : (1 - (1 + u)⁻¹) * (1 + u) = u := by field_simp [h1pu.ne']; ring
    linarith
  have hb2 : (1 - u) / u ≤ 1 / (-Real.log (1 - u)) := by
    rw [div_le_div_iff₀ hu0 hneg]
    have := mul_le_mul_of_nonneg_right (Real.one_sub_inv_le_log_of_pos h1mu) h1mu.le
    have : (1 - (1 - u)⁻¹) * (1 - u) = -u := by field_simp [h1mu.ne']; ring
    nlinarith
  have hsum2 : (1 + u) / u - (1 - u) / u = 2 := by field_simp [hu0.ne']; ring
  have hrew : 1 / (-Real.log (1 - u)) = -(1 / Real.log (1 - u)) := div_neg 1
  linarith

/-- The symmetrized integrand defining `logIntegralTwo` is Bochner-integrable on $(0, 1)$. -/
@[category API, AMS 11]
theorem logIntegralTwo_integrand_integrableOn :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => 1 / Real.log (1 + u) + 1 / Real.log (1 - u)) (Set.Ioo 0 1) := by
  have hcont : ContinuousOn (fun u : ℝ => 1 / Real.log (1 + u) + 1 / Real.log (1 - u))
      (Set.Ioo 0 1) := fun u ⟨hu0, hu1⟩ => by
    have h1 : ContinuousAt (fun x : ℝ => Real.log (1 + x)) u :=
      (Real.continuousAt_log (by linarith)).comp (continuous_const.add continuous_id).continuousAt
    have h2 : ContinuousAt (fun x : ℝ => Real.log (1 - x)) u :=
      (Real.continuousAt_log (by linarith)).comp (continuous_const.sub continuous_id).continuousAt
    exact ((continuousAt_const.div h1 (Real.log_pos (by linarith)).ne').add
      (continuousAt_const.div h2
        (Real.log_neg (by linarith) (by linarith)).ne)).continuousWithinAt
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (hs := by simp) (hC := by simp) (C := (2 : ℝ)))
    (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u ⟨hu0, hu1⟩
  rw [Real.norm_eq_abs, abs_of_pos (logIntegralTwo_integrand_pos hu0 hu1)]
  exact logIntegralTwo_integrand_le_two hu0 hu1

/-- Certifies `0 < logIntegral 2` (ruling out zero-collapse of the Bochner integral). -/
@[category test, AMS 11]
theorem logIntegral_two_pos : 0 < logIntegral 2 := by
  rw [show logIntegral 2 = logIntegralTwo by simp [logIntegral], logIntegralTwo]
  set f : ℝ → ℝ := fun u => 1 / Real.log (1 + u) + 1 / Real.log (1 - u)
  have hae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u ⟨hu0, hu1⟩
    exact (logIntegralTwo_integrand_pos hu0 hu1).le
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hae
    logIntegralTwo_integrand_integrableOn]
  have hsupp : Function.support f ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 :=
    Set.inter_eq_right.mpr fun u ⟨hu0, hu1⟩ => (logIntegralTwo_integrand_pos hu0 hu1).ne'
  simp [hsupp, Real.volume_Ioo]

/-- Offset identity $\operatorname{li}(x) - \operatorname{li}(2) = \int_2^x \frac{dt}{\log t}$ and
monotonicity $\operatorname{li}(2) \le \operatorname{li}(x)$ for $x \ge 2$. -/
@[category API, AMS 11]
theorem logIntegral_offset_and_le {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x - logIntegralTwo = ∫ t in (2 : ℝ)..x, 1 / Real.log t ∧
      logIntegralTwo ≤ logIntegral x := by
  refine ⟨by simp [logIntegral], ?_⟩
  unfold logIntegral
  have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      have ht1 : (1 : ℝ) ≤ t := by linarith [(Set.mem_Icc.mp ht).1]
      exact div_nonneg zero_le_one (Real.log_nonneg ht1)
  linarith

/--
Littlewood's oscillation theorem (1914): both $\{m \ge 2 \mid \operatorname{li}(m) < \pi(m)\}$ and
$\{n \ge 2 \mid \pi(n) < \operatorname{li}(n)\}$ are infinite.
-/
@[category research solved, AMS 11]
theorem littlewood_pi_minus_li_infinite_sign_changes :
    {m : ℕ | 2 ≤ m ∧ logIntegral (m : ℝ) < (Nat.primeCounting m : ℝ)}.Infinite ∧
      {n : ℕ | 2 ≤ n ∧ (Nat.primeCounting n : ℝ) < logIntegral (n : ℝ)}.Infinite := by
  sorry

/--
Unconditional bounds on the first Skewes crossover (Bays–Hudson 2000; Saouter–Trudgian–Demichel
2015; Büthe 2015): $\pi(n) < \operatorname{li}(n)$ for every integer $2 \le n \le 10^{19}$, whereas
some integer $2 \le n < e^{727.95134}$ satisfies $\operatorname{li}(n) < \pi(n)$.
-/
@[category research solved, AMS 11]
theorem skewes_crossover_known_bounds :
    (∀ n : ℕ, 2 ≤ n → n ≤ 10 ^ 19 → (Nat.primeCounting n : ℝ) < logIntegral (n : ℝ)) ∧
      (∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) < Real.exp (72795134 / 100000) ∧
        logIntegral (n : ℝ) < (Nat.primeCounting n : ℝ)) := by
  sorry

def skewes_number.answer : ℕ := sorry

/--
What is Skewes's number, the smallest integer $n \ge 2$ satisfying
$\pi(n) > \operatorname{li}(n)$? The bound $n \ge 2$ avoids the singularity of $\operatorname{li}$
at $1$ and $0 = \pi(0) = \operatorname{li}(0)$.
-/
@[category research open, question value, AMS 11]
theorem skewes_number :
    IsLeast {n : ℕ | 2 ≤ n ∧ logIntegral (n : ℝ) < (Nat.primeCounting n : ℝ)}
      skewes_number.answer := by
  sorry

/--
Does $\pi(n) \le \operatorname{li}(n)$ hold for every integer $n \ge 2$ below $e^{727.95132}$, so
that no crossover precedes the known crossing region near $e^{727.95133}$?
-/
@[category research open, question, AMS 11]
theorem skewes_number.variants.no_crossover_below_known_region :
    ∀ n : ℕ, 2 ≤ n → (n : ℝ) < Real.exp (72795132 / 100000) →
      (Nat.primeCounting n : ℝ) ≤ logIntegral (n : ℝ) := by
  sorry

end SkewesNumber
