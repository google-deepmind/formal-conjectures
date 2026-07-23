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

import FormalConjecturesUtil

/-!
# Erdős Problem 1150

*Reference:* [erdosproblems.com/1150](https://www.erdosproblems.com/1150)
-/

open scoped Polynomial

namespace Erdos1150

/--
Is there some constant $c > 0$ such that, for all large enough $n$ and all polynomials $P$ of
degree $n$ with coefficients in $\{-1, 1\}$,
$$\max_{|z|=1} |P(z)| > (1 + c) \sqrt{n}?$$
-/
@[category research open, AMS 12 30]
theorem erdos_1150 :
    answer(sorry) ↔ ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],  (∀ i ≤ P.natDegree, P.coeff i = - 1 ∨ P.coeff i = 1) → P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n := by
  sorry

/--
The trivial lower bound from Parseval's identity: for any polynomial $P$ of degree $n$ with
coefficients in $\{-1, 1\}$, we have $\max_{|z|=1} |P(z)| \geq \sqrt{n+1}$.

This follows from Parseval's identity:
$$\frac{1}{2\pi} \int_0^{2\pi} |P(e^{i\theta})|^2 d\theta = \sum_{k=0}^{n} |a_k|^2 = n+1$$
since each $|a_k|^2 = 1$.
-/
@[category textbook, AMS 12 30]
theorem erdos_1150.variants.parseval_lower_bound (P : ℂ[X]) (n : ℕ)
    (hcoeff : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1)
    (hdeg : P.natDegree = n) :
    ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1) := by
  -- Evaluate $P$ at the $(n+1)$-th roots of unity $\omega^k$. Discrete Parseval gives
  -- $\sum_k \|P(\omega^k)\|^2 = (n+1) \cdot \sum_i \|a_i\|^2 = (n+1)^2$.
  -- Pigeonhole + sphere lift.
  set N : ℕ := n + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos n
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hω_def
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hNpos.ne'
  have hω_norm : ‖ω‖ = 1 := by
    rw [hω_def, Complex.norm_exp]
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
  have hdeg' : P.natDegree < N := by rw [hN, hdeg]; exact Nat.lt_succ_self n
  -- Each $\|a_i\|^2 = 1$ for $i$ in $\{0, \dots, N-1\}$.
  have hcoeff_sq : ∀ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 = (1 : ℝ) := by
    intro i hi
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rcases hcoeff i (hdeg ▸ hi') with h | h <;> simp [h]
  have hsum_coeff_sq : ∑ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 = (N : ℝ) := by
    rw [Finset.sum_congr rfl hcoeff_sq, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
  -- Apply discrete Parseval: $\sum_k \|P(\omega^k)\|^2 = N \cdot N = N^2$.
  have hsum_eval_sq : ∑ k ∈ Finset.range N, ‖P.eval (ω ^ k)‖ ^ 2 = (N : ℝ) ^ 2 := by
    rw [P.sum_norm_sq_eval_primitiveRoot hω hω_norm hdeg', hsum_coeff_sq]; ring
  -- Pigeonhole: some $k_0$ has $\|P(\omega^{k_0})\|^2 \ge N$.
  have hexists : ∃ k₀ ∈ Finset.range N, ‖P.eval (ω ^ k₀)‖ ^ 2 ≥ (N : ℝ) := by
    by_contra hlt
    push_neg at hlt
    have hsum_lt : ∑ k ∈ Finset.range N, ‖P.eval (ω ^ k)‖ ^ 2 < N * (N : ℝ) := by
      calc ∑ k ∈ Finset.range N, ‖P.eval (ω ^ k)‖ ^ 2
          < ∑ _k ∈ Finset.range N, (N : ℝ) :=
            Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hNpos.ne')
              (fun k hk => hlt k hk)
        _ = N * (N : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum_eval_sq] at hsum_lt
    have : (N : ℝ) ^ 2 < (N : ℝ) ^ 2 := by linarith [sq (N : ℝ)]
    exact lt_irrefl _ this
  obtain ⟨k₀, _, hk₀_bound⟩ := hexists
  have hω_pow_sphere : ω ^ k₀ ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_pow, hω_norm, one_pow]
  -- Conclude: $\sqrt{N} \le \|P(\omega^{k_0})\| \le \sup_{|z|=1} \|P(z)\|$.
  have hsqrt_le : Real.sqrt (N : ℝ) ≤ ‖P.eval (ω ^ k₀)‖ := by
    rw [show ‖P.eval (ω ^ k₀)‖ = Real.sqrt (‖P.eval (ω ^ k₀)‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hk₀_bound
  have hle_sup :
      ‖P.eval (ω ^ k₀)‖ ≤ ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ := by
    -- The sup is bounded: for $\|z\| = 1$, $\|P(z)\| \le \sum_i \|a_i\| \le N$.
    have hbdd : BddAbove
        (Set.range fun z : Metric.sphere (0 : ℂ) 1 => ‖P.eval (z : ℂ)‖) := by
      refine ⟨(N : ℝ), ?_⟩
      rintro _ ⟨⟨z, hz⟩, rfl⟩
      have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      calc ‖P.eval z‖
          = ‖∑ i ∈ Finset.range N, P.coeff i * z ^ i‖ := by
            rw [Polynomial.eval_eq_sum_range' hdeg']
        _ ≤ ∑ i ∈ Finset.range N, ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
        _ = ∑ i ∈ Finset.range N, ‖P.coeff i‖ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, norm_pow, hz1, one_pow, mul_one]
        _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have := hcoeff_sq i hi
            nlinarith [norm_nonneg (P.coeff i)]
        _ = (N : ℝ) := by simp
    exact le_ciSup_of_le hbdd ⟨ω ^ k₀, hω_pow_sphere⟩ le_rfl
  calc Real.sqrt ((n : ℝ) + 1)
      = Real.sqrt (N : ℝ) := by push_cast [hN]; ring_nf
    _ ≤ ‖P.eval (ω ^ k₀)‖ := hsqrt_le
    _ ≤ _ := hle_sup

end Erdos1150
