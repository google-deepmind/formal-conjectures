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

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Kernel-side primitives for the finite Krein interval certificate

This file contains no numerical interval certificate and no RH claim.  It
formalizes the reusable correctness layer needed by the integer checker:

* exact high-precision enclosures for pi and log 2 already proved by Mathlib;
* arbitrary-order Taylor enclosure of real sine/cosine through
  `Complex.exp_bound`;
* Lipschitz transport of a certified center value across a real cell;
* scaled-phase transport, used for the many rational Fourier frequencies in
  the order-19 correction.

The intended consumer is the finite interval `|t| <= 300` part of
`RHKreinExplicitCorrectionV1.PointwiseCertificate`.
-/

open Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinFiniteIntervalKernelV1

/-- The exact Mathlib twenty-decimal enclosure of pi. -/
theorem pi_enclosure :
    (3.14159265358979323846 : ℝ) < Real.pi ∧
      Real.pi < (3.14159265358979323847 : ℝ) :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩

/-- The exact Mathlib ten-decimal enclosure used for the prime-two phase. -/
theorem log_two_enclosure :
    (0.6931471803 : ℝ) < Real.log 2 ∧
      Real.log 2 < (0.6931471808 : ℝ) :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-- Complex Taylor polynomial for `exp (i*x)`, with `n` terms. -/
def expIPartial (n : ℕ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.range n, (((x : ℂ) * I) ^ m) / m.factorial

/-- Arbitrary-order rigorous Taylor enclosure for `exp (i*x)` on `|x| <= 1`.
This is the core high-precision primitive; for fixed rational `x` and `n`,
the polynomial and the error constant reduce to exact arithmetic. -/
theorem expIPartial_error (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : |x| ≤ 1) :
    ‖Complex.exp ((x : ℂ) * I) - expIPartial n x‖ ≤
      |x| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  have hxc : ‖((x : ℂ) * I)‖ ≤ 1 := by
    simpa [Complex.norm_mul, Real.norm_eq_abs] using hx
  have h := Complex.exp_bound (x := ((x : ℂ) * I)) hxc hn
  simpa [expIPartial, Complex.norm_mul, Real.norm_eq_abs] using h

/-- Project the arbitrary-order exponential enclosure to the sine coordinate. -/
theorem sin_expIPartial_error (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : |x| ≤ 1) :
    |Real.sin x - (expIPartial n x).im| ≤
      |x| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  have hnorm := expIPartial_error n x hn hx
  have him := Complex.abs_im_le_norm
    (Complex.exp ((x : ℂ) * I) - expIPartial n x)
  have heq :
      (Complex.exp ((x : ℂ) * I) - expIPartial n x).im =
        Real.sin x - (expIPartial n x).im := by
    simp
  rw [heq] at him
  exact him.trans hnorm

/-- Project the arbitrary-order exponential enclosure to the cosine coordinate. -/
theorem cos_expIPartial_error (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : |x| ≤ 1) :
    |Real.cos x - (expIPartial n x).re| ≤
      |x| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  have hnorm := expIPartial_error n x hn hx
  have hre := Complex.abs_re_le_norm
    (Complex.exp ((x : ℂ) * I) - expIPartial n x)
  have heq :
      (Complex.exp ((x : ℂ) * I) - expIPartial n x).re =
        Real.cos x - (expIPartial n x).re := by
    simp
  rw [heq] at hre
  exact hre.trans hnorm

/-- Convert the complex Taylor norm enclosure into a two-sided real sine
interval.  For rational `x`, both endpoints except for the theorem-proved
remainder are exact rational arithmetic. -/
theorem sin_expIPartial_interval (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : |x| ≤ 1) :
    (expIPartial n x).im -
        |x| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) ≤ Real.sin x ∧
      Real.sin x ≤ (expIPartial n x).im +
        |x| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  have h := sin_expIPartial_error n x hn hx
  rw [abs_sub_le_iff] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Convert the complex Taylor norm enclosure into a two-sided real cosine
interval. -/
theorem cos_expIPartial_interval (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : |x| ≤ 1) :
    (expIPartial n x).re -
        |x| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) ≤ Real.cos x ∧
      Real.cos x ≤ (expIPartial n x).re +
        |x| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  have h := cos_expIPartial_error n x hn hx
  rw [abs_sub_le_iff] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Full sine primitive used by the integer checker: evaluate the Taylor
polynomial at a small center `q`, allow an arbitrary integral number of full
periods, and transport over a certified phase radius. -/
theorem sin_periodic_expIPartial_enclosure
    (n : ℕ) (q x r : ℝ) (k : ℤ)
    (hn : 0 < n) (hq : |q| ≤ 1) (_hr : 0 ≤ r)
    (hx : |x - (q + k * (2 * Real.pi))| ≤ r) :
    (expIPartial n q).im -
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) - r ≤ Real.sin x ∧
      Real.sin x ≤
        (expIPartial n q).im +
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) + r := by
  have hc := sin_expIPartial_interval n q hn hq
  have hlo :
      (expIPartial n q).im -
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) ≤
        Real.sin (q + k * (2 * Real.pi)) := by
    simpa using hc.1
  have hhi :
      Real.sin (q + k * (2 * Real.pi)) ≤
        (expIPartial n q).im +
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
    simpa using hc.2
  have hdist := Real.abs_sin_sub_sin_le x (q + k * (2 * Real.pi))
  rw [abs_sub_le_iff] at hdist
  constructor <;> linarith [hdist.1, hdist.2, hlo, hhi]

/-- Full cosine analogue of `sin_periodic_expIPartial_enclosure`. -/
theorem cos_periodic_expIPartial_enclosure
    (n : ℕ) (q x r : ℝ) (k : ℤ)
    (hn : 0 < n) (hq : |q| ≤ 1) (_hr : 0 ≤ r)
    (hx : |x - (q + k * (2 * Real.pi))| ≤ r) :
    (expIPartial n q).re -
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) - r ≤ Real.cos x ∧
      Real.cos x ≤
        (expIPartial n q).re +
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) + r := by
  have hc := cos_expIPartial_interval n q hn hq
  have hlo :
      (expIPartial n q).re -
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) ≤
        Real.cos (q + k * (2 * Real.pi)) := by
    simpa using hc.1
  have hhi :
      Real.cos (q + k * (2 * Real.pi)) ≤
        (expIPartial n q).re +
          |q| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
    simpa using hc.2
  have hdist := Real.abs_cos_sub_cos_le x (q + k * (2 * Real.pi))
  rw [abs_sub_le_iff] at hdist
  constructor <;> linarith [hdist.1, hdist.2, hlo, hhi]

/-- A certified sine value at a center transports across a cell with no
additional transcendental reasoning. -/
theorem sin_cell_enclosure (x c r lo hi : ℝ)
    (_hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hlo : lo ≤ Real.sin c) (hhi : Real.sin c ≤ hi) :
    lo - r ≤ Real.sin x ∧ Real.sin x ≤ hi + r := by
  have h := Real.abs_sin_sub_sin_le x c
  rw [abs_sub_le_iff] at h
  constructor <;> linarith

/-- The analogous cell transport for cosine. -/
theorem cos_cell_enclosure (x c r lo hi : ℝ)
    (_hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hlo : lo ≤ Real.cos c) (hhi : Real.cos c ≤ hi) :
    lo - r ≤ Real.cos x ∧ Real.cos x ≤ hi + r := by
  have h := Real.abs_cos_sub_cos_le x c
  rw [abs_sub_le_iff] at h
  constructor <;> linarith

/-- Scaling a real phase scales its cell radius by the absolute frequency. -/
theorem scaled_phase_radius (a x c r : ℝ) (hx : |x - c| ≤ r) :
    |a * x - a * c| ≤ |a| * r := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg a)

/-- Sine cell transport for a scaled Fourier phase. -/
theorem sin_scaled_cell_enclosure (a x c r lo hi : ℝ)
    (hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hlo : lo ≤ Real.sin (a * c)) (hhi : Real.sin (a * c) ≤ hi) :
    lo - |a| * r ≤ Real.sin (a * x) ∧
      Real.sin (a * x) ≤ hi + |a| * r := by
  exact sin_cell_enclosure (a * x) (a * c) (|a| * r) lo hi
    (mul_nonneg (abs_nonneg a) hr) (scaled_phase_radius a x c r hx) hlo hhi

/-- Cosine cell transport for a scaled Fourier phase. -/
theorem cos_scaled_cell_enclosure (a x c r lo hi : ℝ)
    (hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hlo : lo ≤ Real.cos (a * c)) (hhi : Real.cos (a * c) ≤ hi) :
    lo - |a| * r ≤ Real.cos (a * x) ∧
      Real.cos (a * x) ≤ hi + |a| * r := by
  exact cos_cell_enclosure (a * x) (a * c) (|a| * r) lo hi
    (mul_nonneg (abs_nonneg a) hr) (scaled_phase_radius a x c r hx) hlo hhi

/-- Explicit real Taylor polynomial centered at `c`.  Unlike
`taylorWithinEval`, this expression contains only ordinary iterated derivatives,
so after the derivative formulas are proved its coefficients can be checked by
exact arithmetic. -/
def centeredTaylorEval (f : ℝ → ℝ) (n : ℕ) (c x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (((Nat.factorial k : ℕ) : ℝ)⁻¹ * (x - c) ^ k) * iteratedDeriv k f c

/-- On a unique-differentiability set, Mathlib's within-Taylor polynomial is
the explicit ordinary-derivative polynomial above. -/
theorem taylorWithinEval_eq_centeredTaylor
    (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (c x : ℝ)
    (hs : UniqueDiffOn ℝ s) (hc : c ∈ s) (hf : ContDiffAt ℝ n f c) :
    taylorWithinEval f n s c x = centeredTaylorEval f n c x := by
  rw [taylor_within_apply]
  unfold centeredTaylorEval
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkdiff : ContDiffAt ℝ k f c := hf.of_le (by exact_mod_cast hkn)
  rw [iteratedDerivWithin_eq_iteratedDeriv hs hkdiff hc]
  simp only [smul_eq_mul]

/-- The centered polynomial evaluates to the function at its center. -/
theorem centeredTaylorEval_self (f : ℝ → ℝ) (n : ℕ) (c : ℝ)
    (hf : ContDiffAt ℝ n f c) :
    centeredTaylorEval f n c c = f c := by
  rw [← taylorWithinEval_eq_centeredTaylor f n Set.univ c c
    uniqueDiffOn_univ (Set.mem_univ c) hf]
  exact taylorWithinEval_self f n Set.univ c

/-- Degree-seven Lagrange remainder bound in a form tailored to the committed
finite-interval certificate.  The only analytic input beyond smoothness is a
uniform bound on the eighth ordinary derivative. -/
theorem centeredTaylor7_remainder_of_ne
    (f : ℝ → ℝ) (c x M : ℝ) (hcx : c ≠ x)
    (hf : ContDiff ℝ 8 f)
    (hM : ∀ y : ℝ, |iteratedDeriv 8 f y| ≤ M) :
    |f x - centeredTaylorEval f 7 c x| ≤
      M * |x - c| ^ 8 / (40320 : ℝ) := by
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := f) (x := x) (x₀ := c) (n := 7) hcx hf.contDiffOn
  have htaylor :
      taylorWithinEval f 7 (Set.uIcc c x) c x =
        centeredTaylorEval f 7 c x := by
    apply taylorWithinEval_eq_centeredTaylor
    · exact uniqueDiffOn_uIcc hcx
    · exact Set.left_mem_uIcc
    · exact hf.contDiffAt.of_le (by norm_num)
  rw [← htaylor, hrem, abs_div, abs_mul, abs_pow]
  have hMy := hM y
  have hM0 : 0 ≤ M := (abs_nonneg (iteratedDeriv 8 f y)).trans hMy
  have hpow : 0 ≤ |x - c| ^ 8 := pow_nonneg (abs_nonneg _) _
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul hMy le_rfl hpow hM0) (by norm_num)

/-- Cell-radius version of the degree-seven remainder bound. -/
theorem centeredTaylor7_cell_remainder_of_ne
    (f : ℝ → ℝ) (c x r M : ℝ) (hcx : c ≠ x)
    (_hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hf : ContDiff ℝ 8 f)
    (hM : ∀ y : ℝ, |iteratedDeriv 8 f y| ≤ M) :
    |f x - centeredTaylorEval f 7 c x| ≤
      M * r ^ 8 / (40320 : ℝ) := by
  have hbase := centeredTaylor7_remainder_of_ne f c x M hcx hf hM
  have hM0 : 0 ≤ M := (abs_nonneg (iteratedDeriv 8 f c)).trans (hM c)
  have hp := pow_le_pow_left₀ (abs_nonneg (x - c)) hx 8
  exact hbase.trans (by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hp hM0
    · norm_num)

/-- A lower bound for the explicit degree-seven polynomial promotes to a
lower bound for the analytic function after subtracting the rigorous
eighth-derivative remainder budget. -/
theorem lower_of_centeredTaylor7
    (f : ℝ → ℝ) (c x r M L : ℝ)
    (hcx : c ≠ x) (hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hf : ContDiff ℝ 8 f)
    (hM : ∀ y : ℝ, |iteratedDeriv 8 f y| ≤ M)
    (hpoly : L ≤ centeredTaylorEval f 7 c x) :
    L - M * r ^ 8 / (40320 : ℝ) ≤ f x := by
  have hrem := centeredTaylor7_cell_remainder_of_ne f c x r M hcx hr hx hf hM
  rw [abs_sub_le_iff] at hrem
  linarith

end AEGIS.RHKreinFiniteIntervalKernelV1

#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.pi_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.log_two_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.expIPartial_error
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.sin_expIPartial_error
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.cos_expIPartial_error
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.sin_expIPartial_interval
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.cos_expIPartial_interval
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.sin_periodic_expIPartial_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.cos_periodic_expIPartial_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.sin_cell_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.cos_cell_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.sin_scaled_cell_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.cos_scaled_cell_enclosure
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.taylorWithinEval_eq_centeredTaylor
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.centeredTaylor7_remainder_of_ne
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.centeredTaylor7_cell_remainder_of_ne
#print axioms AEGIS.RHKreinFiniteIntervalKernelV1.lower_of_centeredTaylor7
