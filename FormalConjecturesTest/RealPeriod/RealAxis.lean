/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import FormalConjecturesTest.RealPeriod.Conjugation
import FormalConjecturesTest.RealPeriod.HalfPeriods

/-!
# The Weierstrass function of a real lattice on the real axis

Let $\Lambda$ be a real lattice, one stable under complex conjugation, with least positive real
period $\Omega$. Then $\wp$ and $\wp'$ take real values on the real axis
(`PeriodPair.IsReal.coe_weierstrassPRe`, `PeriodPair.IsReal.coe_derivWeierstrassPRe`); we write
`PeriodPair.weierstrassPRe` and `PeriodPair.derivWeierstrassPRe` for the real functions. On
$(0, \Omega / 2)$ the derivative does not vanish, because its zeros are the half-periods
(`PeriodPair.derivWeierstrassP_eq_zero_iff`) and $2t \in (0, \Omega)$ is not a period; it is
negative because $\wp'(t) \sim -2 t^{-3}$ as $t \to 0^+$. So $\wp$ decreases strictly from
$+\infty$ at $0^+$ to $e_1 := \wp(\Omega / 2)$, and $\wp'(\Omega / 2) = 0$. Hence $e_1$ is a root
of $4x^3 - g_2 x - g_3$, and the largest real one: a larger real root $e$ would be $\wp(t)$ for some
$t \in (0, \Omega / 2)$ with $\wp'(t)^2 = 4e^3 - g_2 e - g_3 = 0$.

The substitution $x = \wp(t)$ in the elliptic integral, with $dx = \wp'(t) \, dt$ and
$\sqrt{4x^3 - g_2 x - g_3} = |\wp'(t)|$, gives the classical formula
$$\int_{e_1}^{\infty} \frac{dx}{\sqrt{4x^3 - g_2 x - g_3}} = \frac{\Omega}{2}$$
(`PeriodPair.IsReal.integral_inv_sqrt_eq_half`): DLMF 23.6.34 and 23.6.36, Pastras (3.1) and
(A.1). The real lattices with $\Delta > 0$ (rectangular) and $\Delta < 0$ (rhombic) are treated
uniformly: only the least positive real period enters.

*References:*
- [DLMF](https://dlmf.nist.gov/23.5), §23.5(i)–(iv) and §23.6(iv), equations 23.6.30, 23.6.34,
    23.6.36
- [Pas2017] Georgios Pastras. Four Lectures on Weierstrass Elliptic Function and Applications in
    Classical and Quantum Mechanics, §1 equations (1.31)–(1.32), §3.1 equation (3.1) and the
    discussion of Figure 3, Appendix A, https://arxiv.org/abs/1706.07371
- [Cre1997] John E. Cremona. Algorithms for Modular Elliptic Curves, 2nd edition, Section 3.7,
    https://johncremona.github.io/book/fulltext/index.html
-/

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace PeriodPair

noncomputable section

variable (L : PeriodPair)

/- ## Conjugation -/

/-- The Weierstrass function of the conjugate lattice is the conjugate of the Weierstrass function
at the conjugate point. -/
lemma weierstrassP_conjugate (z : ℂ) : ℘[L.conjugate] z = conj (℘[L] (conj z)) := by
  simp only [weierstrassP, Complex.conj_tsum]
  rw [← L.conjugateLatticeEquiv.tsum_eq]
  exact tsum_congr fun l ↦ by simp [conjugateLatticeEquiv]

/-- The same for $\wp'$. -/
lemma derivWeierstrassP_conjugate (z : ℂ) : ℘'[L.conjugate] z = conj (℘'[L] (conj z)) := by
  simp only [derivWeierstrassP, map_neg, Complex.conj_tsum]
  rw [← L.conjugateLatticeEquiv.tsum_eq]
  exact congrArg Neg.neg (tsum_congr fun l ↦ by
    simp [conjugateLatticeEquiv, Complex.conj_ofNat])

variable {L}

/-- For a real lattice, $\overline{\wp(z)} = \wp(\overline{z})$. -/
lemma IsReal.conj_weierstrassP (hL : L.IsReal) (z : ℂ) : conj (℘[L] z) = ℘[L] (conj z) := by
  have h := L.weierstrassP_conjugate (conj z)
  rw [weierstrassP_congr hL, Complex.conj_conj] at h
  exact h.symm

/-- For a real lattice, $\overline{\wp'(z)} = \wp'(\overline{z})$. -/
lemma IsReal.conj_derivWeierstrassP (hL : L.IsReal) (z : ℂ) :
    conj (℘'[L] z) = ℘'[L] (conj z) := by
  have h := L.derivWeierstrassP_conjugate (conj z)
  rw [derivWeierstrassP_congr hL, Complex.conj_conj] at h
  exact h.symm

/- ## `℘` on the real axis -/

variable (L)

/-- The real part of $\wp$ on the real axis. For a real lattice this is $\wp$ itself. -/
def weierstrassPRe (t : ℝ) : ℝ := (℘[L] (t : ℂ)).re

/-- The real part of $\wp'$ on the real axis. For a real lattice this is $\wp'$ itself. -/
def derivWeierstrassPRe (t : ℝ) : ℝ := (℘'[L] (t : ℂ)).re

variable {L}

/-- For a real lattice, $\wp$ is real on the real axis. -/
lemma IsReal.coe_weierstrassPRe (hL : L.IsReal) (t : ℝ) :
    (L.weierstrassPRe t : ℂ) = ℘[L] t :=
  Complex.conj_eq_iff_re.mp (by rw [hL.conj_weierstrassP, Complex.conj_ofReal])

/-- For a real lattice, $\wp'$ is real on the real axis. -/
lemma IsReal.coe_derivWeierstrassPRe (hL : L.IsReal) (t : ℝ) :
    (L.derivWeierstrassPRe t : ℂ) = ℘'[L] t :=
  Complex.conj_eq_iff_re.mp (by rw [hL.conj_derivWeierstrassP, Complex.conj_ofReal])

variable (L)

/-- Off the lattice, the real function has derivative the real part of $\wp'$. -/
lemma hasDerivAt_weierstrassPRe {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    HasDerivAt L.weierstrassPRe (L.derivWeierstrassPRe t) t :=
  (L.hasDerivAt_weierstrassP ht).real_of_complex

lemma continuousAt_weierstrassPRe {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    ContinuousAt L.weierstrassPRe t :=
  (L.hasDerivAt_weierstrassPRe ht).continuousAt

lemma continuousAt_derivWeierstrassPRe {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    ContinuousAt L.derivWeierstrassPRe t :=
  (L.hasDerivAt_derivWeierstrassP ht).real_of_complex.continuousAt

variable {L}

/-- The differential equation $\wp'^2 = 4 \wp^3 - g_2 \wp - g_3$ on the real axis of a real lattice,
whose invariants are real. -/
lemma IsReal.derivWeierstrassPRe_sq (hL : L.IsReal) {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    L.derivWeierstrassPRe t ^ 2 =
      4 * L.weierstrassPRe t ^ 3 - L.g₂.re * L.weierstrassPRe t - L.g₃.re := by
  have hsq := L.derivWeierstrassP_sq (t : ℂ) ht
  have h₂ : L.g₂ = (L.g₂.re : ℂ) := (Complex.conj_eq_iff_re.mp hL.conj_g₂).symm
  have h₃ : L.g₃ = (L.g₃.re : ℂ) := (Complex.conj_eq_iff_re.mp hL.conj_g₃).symm
  rw [← hL.coe_derivWeierstrassPRe, ← hL.coe_weierstrassPRe, h₂, h₃] at hsq
  exact_mod_cast hsq

variable (L)

/- ## Behaviour at the pole -/

/-- Positive powers preserve the punctured-from-the-right neighbourhood of $0$. -/
private lemma tendsto_pow_nhdsGT_zero {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun t : ℝ ↦ t ^ n) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa [zero_pow hn] using
      ((continuous_pow n).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht using pow_pos (mem_Ioi.mp ht) n

/-- The reciprocal of a positive power blows up at $0^+$. -/
private lemma tendsto_inv_pow_nhdsGT_zero {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹) (𝓝[>] 0) atTop := by
  simpa [Pi.inv_def] using (tendsto_pow_nhdsGT_zero hn).inv_tendsto_nhdsGT_zero

/-- $\wp(t) = \wp^{\circ}(t) + t^{-2} \to +\infty$ as $t \to 0^+$. -/
lemma tendsto_weierstrassPRe_nhdsGT_zero : Tendsto L.weierstrassPRe (𝓝[>] 0) atTop := by
  have hreg : Tendsto (fun t : ℝ ↦ (℘[L - (0 : ℂ)] (t : ℂ)).re) (𝓝[>] 0) (𝓝 0) := by
    have h₁ : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
    have h₂ : Tendsto ℘[L - (0 : ℂ)] (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using (L.analyticAt_weierstrassPExcept 0).continuousAt.tendsto
    have h₃ := (Complex.continuous_re.tendsto (0 : ℂ)).comp (h₂.comp h₁)
    simpa [Function.comp_def] using h₃.mono_left nhdsWithin_le_nhds
  have hpole : Tendsto (fun t : ℝ ↦ 1 / t ^ 2) (𝓝[>] 0) atTop := by
    simpa [one_div] using tendsto_inv_pow_nhdsGT_zero two_ne_zero
  have heq : ∀ t : ℝ, L.weierstrassPRe t = (℘[L - (0 : ℂ)] (t : ℂ)).re + 1 / t ^ 2 := by
    intro t
    rw [weierstrassPRe, L.weierstrassP_eq (t : ℂ), Complex.add_re,
      show (1 : ℂ) / (t : ℂ) ^ 2 = ((1 / t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [show L.weierstrassPRe = fun t : ℝ ↦ (℘[L - (0 : ℂ)] (t : ℂ)).re + 1 / t ^ 2 from funext heq]
  refine Filter.tendsto_atTop_mono' _ ?_
    (Filter.tendsto_atTop_add_const_right _ (-1 : ℝ) hpole)
  filter_upwards [hreg.eventually (eventually_ge_nhds (by norm_num : (-1 : ℝ) < 0))]
    with t ht using by linarith

/-- $\wp'(t) = \wp'^{\circ}(t) - 2 t^{-3} < 0$ for small $t > 0$. -/
lemma eventually_derivWeierstrassPRe_neg : ∀ᶠ t in 𝓝[>] 0, L.derivWeierstrassPRe t < 0 := by
  have hreg : Tendsto (fun t : ℝ ↦ (℘'[L - (0 : ℂ)] (t : ℂ)).re) (𝓝[>] 0) (𝓝 0) := by
    have h₁ : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
    have h₂ : Tendsto ℘'[L - (0 : ℂ)] (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using (L.analyticAt_derivWeierstrassPExcept 0).continuousAt.tendsto
    have h₃ := (Complex.continuous_re.tendsto (0 : ℂ)).comp (h₂.comp h₁)
    simpa [Function.comp_def] using h₃.mono_left nhdsWithin_le_nhds
  have hpole : Tendsto (fun t : ℝ ↦ 2 / t ^ 3) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_pow_nhdsGT_zero three_ne_zero).const_mul_atTop (r := (2:ℝ)) (by norm_num)
  have heq : ∀ t : ℝ, L.derivWeierstrassPRe t = (℘'[L - (0 : ℂ)] (t : ℂ)).re - 2 / t ^ 3 := by
    intro t
    have h := L.derivWeierstrassPExcept_zero_eq (t : ℂ)
    rw [derivWeierstrassPRe, show ℘'[L] (t : ℂ) = ℘'[L - (0 : ℂ)] (t : ℂ) - 2 / (t : ℂ) ^ 3 by
      rw [h]; ring, Complex.sub_re,
      show (2 : ℂ) / (t : ℂ) ^ 3 = ((2 / t ^ 3 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [show L.derivWeierstrassPRe = fun t : ℝ ↦ (℘'[L - (0 : ℂ)] (t : ℂ)).re - 2 / t ^ 3 from
    funext heq]
  filter_upwards [hreg.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)),
    hpole.eventually (eventually_gt_atTop (1 : ℝ))] with t h1 h2
  linarith

/- ## The least positive real period -/

variable {L} {Ω : ℝ} (hΩ : IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} Ω)
include hΩ

/-- No real number strictly between $0$ and the least positive real period is a period. -/
lemma notMem_lattice_of_lt {t : ℝ} (h0 : 0 < t) (ht : t < Ω) : (t : ℂ) ∉ L.lattice :=
  fun hmem ↦ absurd (hΩ.2 ⟨hmem, h0⟩) ht.not_ge

/-- $\wp'$ vanishes at the real half-period $\Omega / 2$. -/
lemma derivWeierstrassPRe_half : L.derivWeierstrassPRe (Ω / 2) = 0 := by
  have h := L.derivWeierstrassP_eq_zero_of_two_mul_mem (z := ((Ω / 2 : ℝ) : ℂ))
    (by rw [show (2 : ℂ) * ((Ω / 2 : ℝ) : ℂ) = (Ω : ℂ) by push_cast; ring]; exact hΩ.1.1)
  rw [derivWeierstrassPRe, h, Complex.zero_re]

/-- $\wp'$ does not vanish on $(0, \Omega / 2)$: its zeros are the half-periods, and $2t$ is not a
period for $0 < 2t < \Omega$. -/
lemma derivWeierstrassP_ne_zero_of_lt_half {t : ℝ} (h0 : 0 < t) (ht : t < Ω / 2) :
    ℘'[L] t ≠ 0 := by
  have hΩpos : 0 < Ω := hΩ.1.2
  intro hzero
  have h2 := L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero
    (notMem_lattice_of_lt hΩ h0 (by linarith)) hzero
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring] at h2
  exact notMem_lattice_of_lt hΩ (by linarith) (by linarith) h2

/-- For a real lattice, $\wp' < 0$ on $(0, \Omega / 2)$: it is real, continuous, nonvanishing there,
and negative near $0^+$, so it is negative throughout by the intermediate value theorem. -/
lemma IsReal.derivWeierstrassPRe_neg_of_lt_half (hL : L.IsReal) {t : ℝ} (h0 : 0 < t)
    (ht : t < Ω / 2) : L.derivWeierstrassPRe t < 0 := by
  have hΩpos : 0 < Ω := hΩ.1.2
  -- The derivative is real and nonvanishing on `(0, Ω/2)`.
  have hne : ∀ s : ℝ, 0 < s → s < Ω / 2 → L.derivWeierstrassPRe s ≠ 0 := fun s hs hs' hzero ↦
    derivWeierstrassP_ne_zero_of_lt_half hΩ hs hs'
      (by rw [← hL.coe_derivWeierstrassPRe, hzero, Complex.ofReal_zero])
  by_contra hge
  have hpos : 0 < L.derivWeierstrassPRe t := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm (hne t h0 ht))
  -- Near `0` it is negative, so it vanishes somewhere in between.
  obtain ⟨t₁, ht₁neg, ht₁⟩ :=
    ((L.eventually_derivWeierstrassPRe_neg).and (Ioo_mem_nhdsGT h0)).exists
  have hcont : ContinuousOn L.derivWeierstrassPRe (Icc t₁ t) := fun s hs ↦
    (L.continuousAt_derivWeierstrassPRe (notMem_lattice_of_lt hΩ (by linarith [hs.1, ht₁.1])
      (by linarith [hs.2, ht]))).continuousWithinAt
  obtain ⟨t₂, ht₂, hzero⟩ := intermediate_value_Ioo ht₁.2.le hcont ⟨ht₁neg, hpos⟩
  exact hne t₂ (by linarith [ht₂.1, ht₁.1]) (by linarith [ht₂.2]) hzero

/-- For a real lattice, $\wp$ is strictly decreasing on $(0, \Omega / 2]$. -/
lemma IsReal.strictAntiOn_weierstrassPRe (hL : L.IsReal) :
    StrictAntiOn L.weierstrassPRe (Ioc 0 (Ω / 2)) := by
  have hΩpos : 0 < Ω := hΩ.1.2
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 (Ω / 2)) (fun s hs ↦
    (L.continuousAt_weierstrassPRe (notMem_lattice_of_lt hΩ hs.1
      (by linarith [hs.2]))).continuousWithinAt) fun s hs ↦ ?_
  rw [interior_Ioc] at hs
  rw [(L.hasDerivAt_weierstrassPRe (notMem_lattice_of_lt hΩ hs.1 (by linarith [hs.2]))).deriv]
  exact hL.derivWeierstrassPRe_neg_of_lt_half hΩ hs.1 hs.2

/-- For a real lattice, $\wp$ maps $(0, \Omega / 2)$ onto $(\wp(\Omega / 2), \infty)$. -/
lemma IsReal.image_weierstrassPRe_Ioo (hL : L.IsReal) :
    L.weierstrassPRe '' Ioo 0 (Ω / 2) = Ioi (L.weierstrassPRe (Ω / 2)) := by
  have hΩpos : 0 < Ω := hΩ.1.2
  refine subset_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact hL.strictAntiOn_weierstrassPRe hΩ ⟨ht.1, ht.2.le⟩ ⟨by linarith, le_rfl⟩ ht.2
  · -- `℘ → +∞` at `0⁺`, so some `t'` has `℘(t') > y`; then the intermediate value theorem.
    obtain ⟨t', hyt', ht'⟩ :=
      (((L.tendsto_weierstrassPRe_nhdsGT_zero).eventually (eventually_gt_atTop y)).and
        (Ioo_mem_nhdsGT (by linarith : (0:ℝ) < Ω / 2))).exists
    have hcont : ContinuousOn L.weierstrassPRe (Icc t' (Ω / 2)) := fun s hs ↦
      (L.continuousAt_weierstrassPRe (notMem_lattice_of_lt hΩ (by linarith [hs.1, ht'.1])
        (by linarith [hs.2]))).continuousWithinAt
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Ioo' ht'.2.le hcont ⟨hy, hyt'⟩
    exact ⟨t, ⟨by linarith [ht.1, ht'.1], ht.2⟩, rfl⟩

/-- $e_1 := \wp(\Omega / 2)$ is a root of $4x^3 - g_2 x - g_3$, since $\wp'(\Omega / 2) = 0$. -/
lemma IsReal.isRoot_weierstrassPRe_half (hL : L.IsReal) :
    4 * L.weierstrassPRe (Ω / 2) ^ 3 - L.g₂.re * L.weierstrassPRe (Ω / 2) - L.g₃.re = 0 := by
  have hΩpos : 0 < Ω := hΩ.1.2
  have h := hL.derivWeierstrassPRe_sq (t := Ω / 2)
    (notMem_lattice_of_lt hΩ (by linarith) (by linarith))
  rw [derivWeierstrassPRe_half hΩ] at h
  linarith [h]

/-- $e_1 = \wp(\Omega / 2)$ is the largest real root of $4x^3 - g_2 x - g_3$: a real root
$x > e_1$ is $\wp(t)$ for some $t \in (0, \Omega / 2)$, where $\wp'(t)^2 = 4x^3 - g_2 x - g_3 = 0$
contradicts `PeriodPair.derivWeierstrassP_ne_zero_of_lt_half`. -/
lemma IsReal.le_weierstrassPRe_half_of_isRoot (hL : L.IsReal) {x : ℝ}
    (hx : 4 * x ^ 3 - L.g₂.re * x - L.g₃.re = 0) : x ≤ L.weierstrassPRe (Ω / 2) := by
  have hΩpos : 0 < Ω := hΩ.1.2
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht, hxt⟩ : x ∈ L.weierstrassPRe '' Ioo 0 (Ω / 2) := by
    rw [hL.image_weierstrassPRe_Ioo hΩ]; exact hlt
  have h := hL.derivWeierstrassPRe_sq (notMem_lattice_of_lt hΩ ht.1 (by linarith [ht.2]))
  rw [hxt, hx] at h
  exact (hL.derivWeierstrassPRe_neg_of_lt_half hΩ ht.1 ht.2).ne
    (pow_eq_zero_iff two_ne_zero |>.mp h)

/-- On $(0, \Omega / 2)$ the substitution $x = \wp(t)$ has Jacobian
$|\wp'(t)| = \sqrt{4 \wp(t)^3 - g_2 \wp(t) - g_3} \neq 0$. -/
lemma IsReal.abs_derivWeierstrassPRe_mul_inv_sqrt (hL : L.IsReal) {t : ℝ} (h0 : 0 < t)
    (ht : t < Ω / 2) : |L.derivWeierstrassPRe t| *
      (√(4 * L.weierstrassPRe t ^ 3 - L.g₂.re * L.weierstrassPRe t - L.g₃.re))⁻¹ = 1 := by
  have hΩpos : 0 < Ω := hΩ.1.2
  rw [← hL.derivWeierstrassPRe_sq (notMem_lattice_of_lt hΩ h0 (by linarith)),
    Real.sqrt_sq_eq_abs]
  exact mul_inv_cancel₀ (abs_ne_zero.mpr (hL.derivWeierstrassPRe_neg_of_lt_half hΩ h0 ht).ne)

/-- **The elliptic integral of a real lattice**: the least positive real period is twice the
integral of $dx / \sqrt{4x^3 - g_2 x - g_3}$ from the largest real root $e_1 = \wp(\Omega / 2)$ to
$\infty$. The substitution $x = \wp(t)$, $t \in (0, \Omega / 2)$, has $dx = \wp'(t) \, dt$ and
$\sqrt{4x^3 - g_2 x - g_3} = -\wp'(t)$, so the integrand becomes $1$. -/
theorem IsReal.integral_inv_sqrt_eq_half (hL : L.IsReal) :
    ∫ x in Ioi (L.weierstrassPRe (Ω / 2)), (√(4 * x ^ 3 - L.g₂.re * x - L.g₃.re))⁻¹ = Ω / 2 := by
  have hΩpos : 0 < Ω := hΩ.1.2
  rw [← hL.image_weierstrassPRe_Ioo hΩ,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (f' := L.derivWeierstrassPRe)
      (fun x hx ↦ (L.hasDerivAt_weierstrassPRe (notMem_lattice_of_lt hΩ hx.1
        (by linarith [hx.2]))).hasDerivWithinAt)
      ((hL.strictAntiOn_weierstrassPRe hΩ).injOn.mono Ioo_subset_Ioc_self),
    setIntegral_congr_fun (g := fun _ ↦ (1 : ℝ)) measurableSet_Ioo (fun x hx ↦ by
      simpa [smul_eq_mul] using hL.abs_derivWeierstrassPRe_mul_inv_sqrt hΩ hx.1 hx.2),
    setIntegral_const, Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul, mul_one, sub_zero]

end

end PeriodPair
