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

import FormalConjectures.Util.ProblemImports

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
  -- Strategy: evaluate P at the (n+1)-th roots of unity ω^k.
  -- Discrete Parseval gives ∑_{k=0}^n ‖P.eval (ω^k)‖² = (n+1) * ∑|aᵢ|² = (n+1)².
  -- So some ‖P.eval (ω^{k₀})‖² ≥ n+1, giving ⨆ ≥ √(n+1).
  set N : ℕ := n + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos n
  -- ω : primitive (n+1)-th root of unity in ℂ.
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hω_def
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hNpos.ne'
  have hω_norm : ‖ω‖ = 1 := by
    rw [hω_def, Complex.norm_exp]
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
  have hω_ne_zero : ω ≠ 0 := fun h => by simp [h] at hω_norm
  -- Each |aᵢ|² = 1 for i ≤ n.
  have hcoeff_sq : ∀ i, i ≤ n → ‖P.coeff i‖ ^ 2 = 1 := by
    intro i hi
    rcases hcoeff i (hdeg ▸ hi) with h | h <;> simp [h]
  -- Sum of |aᵢ|² over the degree range equals n+1.
  have hsum_coeff_sq : ∑ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 = (N : ℝ) := by
    have : ∀ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 = (1 : ℝ) := by
      intro i hi
      exact hcoeff_sq i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
  -- Key identity: ∑_{k=0}^n ‖P.eval (ω^k)‖² = N * ∑ |aᵢ|² = N².
  -- The proof requires expanding P.eval(ω^k) = ∑ a_i · ω^(k*i), squaring via
  -- z * conj(z), swapping the double sum, and applying the orthogonality
  -- relation ∑_{k=0}^{N-1} ω^(k*(i-j)) = if i = j then N else 0 (using
  -- ω^N = 1 and the geometric series formula). This is the genuine algebraic
  -- heart of the proof and the longest sub-goal.
  have hsum_eval_sq :
      ∑ k ∈ Finset.range N, ‖P.eval (ω ^ k)‖ ^ 2 = (N : ℝ) ^ 2 := by
    have hdeg' : P.natDegree < N := by rw [hN, hdeg]; exact Nat.lt_succ_self n
    -- Each coefficient is real (±1 or 0).
    have hcoeff_conj : ∀ i ∈ Finset.range N,
        (starRingEnd ℂ) (P.coeff i) = P.coeff i := by
      intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      rcases hcoeff i (hdeg ▸ hi') with h | h <;> simp [h]
    -- ω^N = 1.
    have hω_pow_N : ω ^ N = 1 := hω.pow_eq_one
    -- Orthogonality: ∑_{k<N} (ω^d)^k = 0 when 0 < d < N.
    have hortho_ne : ∀ d : ℕ, 0 < d → d < N →
        ∑ k ∈ Finset.range N, (ω ^ d) ^ k = 0 := by
      intro d hd_pos hd_lt
      have hne : ω ^ d ≠ 1 := hω.pow_ne_one_of_pos_of_lt hd_pos.ne' hd_lt
      have hpowN : (ω ^ d) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω_pow_N, one_pow]
      rw [geom_sum_eq hne N, hpowN, sub_self, zero_div]
    -- ‖z‖² = z * conj(z) as a complex number.
    have hnorm_sq_cast : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
      intro z
      rw [RCLike.mul_conj (K := ℂ)]; push_cast; rfl
    -- star ω = ω⁻¹ since ω is on the unit circle.
    have hstar_ω : (starRingEnd ℂ) ω = ω⁻¹ := (RCLike.inv_eq_conj hω_norm).symm
    -- Orthogonality (pair form): ∑_k ω^(k*a) * star(ω^(k*b)) = if a = b then N else 0.
    have hortho_pair : ∀ a b : ℕ, a < N → b < N →
        ∑ k ∈ Finset.range N, ω ^ (k * a) * (starRingEnd ℂ) (ω ^ (k * b)) =
        if a = b then (N : ℂ) else 0 := by
      intro a b ha hb
      -- Rewrite star(ω^(k*b)) = (ω⁻¹)^(k*b), then combine: factor = (ω^a * ω⁻¹^b)^k.
      have hstar_pow : ∀ k, (starRingEnd ℂ) (ω ^ (k * b)) = (ω⁻¹) ^ (k * b) := by
        intro k; rw [map_pow, hstar_ω]
      -- Set ζ = ω^a * (ω⁻¹)^b. Then the summand for each k is ζ^k.
      set ζ : ℂ := ω ^ a * (ω⁻¹) ^ b with hζ_def
      have hsumm : ∀ k, ω ^ (k * a) * (starRingEnd ℂ) (ω ^ (k * b)) = ζ ^ k := by
        intro k
        rw [hstar_pow k, mul_comm k a, pow_mul, mul_comm k b, pow_mul, ← mul_pow, hζ_def]
      conv_lhs => rw [show (fun k => ω ^ (k * a) * (starRingEnd ℂ) (ω ^ (k * b))) = (fun k => ζ ^ k) from funext hsumm]
      -- ζ^N = 1.
      have hζN : ζ ^ N = 1 := by
        rw [hζ_def, mul_pow, ← pow_mul, ← pow_mul, mul_comm a N, mul_comm b N,
            pow_mul, pow_mul, hω_pow_N, inv_pow, hω_pow_N, inv_one, one_pow, one_pow,
            mul_one]
      split_ifs with hab
      · -- a = b: ζ = 1
        subst hab
        have hζ_one : ζ = 1 := by
          rw [hζ_def, ← mul_pow, mul_inv_cancel₀ hω_ne_zero, one_pow]
        simp [hζ_one]
      · -- a ≠ b: ζ ≠ 1 (else ω^a = ω^b ⇒ a = b mod N ⇒ a = b in [0, N-1])
        have hζ_ne_one : ζ ≠ 1 := by
          intro h
          apply hab
          -- ζ = ω^a * (ω^b)⁻¹ = 1 ⇔ ω^a = ω^b
          have hpow_b_ne : ω ^ b ≠ 0 := pow_ne_zero _ hω_ne_zero
          have hζ' : ω ^ a * (ω ^ b)⁻¹ = 1 := by rwa [hζ_def, inv_pow] at h
          have : ω ^ a = ω ^ b := by
            field_simp at hζ'; exact hζ'
          exact hω.pow_inj ha hb this
        rw [geom_sum_eq hζ_ne_one N, hζN, sub_self, zero_div]
    -- Cast everything to ℂ and work there.
    apply_fun ((↑) : ℝ → ℂ) using Complex.ofReal_injective
    push_cast
    -- Goal now: ∑ k, (‖P.eval (ω^k)‖ : ℂ)^2 = (N : ℂ)^2
    -- Convert each summand via hnorm_sq_cast.
    have hlhs : ∑ k ∈ Finset.range N, ((‖P.eval (ω ^ k)‖ : ℂ) ^ 2) =
        ∑ k ∈ Finset.range N, P.eval (ω ^ k) * (starRingEnd ℂ) (P.eval (ω ^ k)) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      have := hnorm_sq_cast (P.eval (ω ^ k))
      push_cast at this
      exact this
    rw [hlhs]
    -- Expand P.eval(ω^k) = ∑ i, P.coeff i * ω^(k*i)
    have hexpand : ∀ k, P.eval (ω ^ k) =
        ∑ i ∈ Finset.range N, P.coeff i * ω ^ (k * i) := by
      intro k
      rw [Polynomial.eval_eq_sum_range' hdeg']
      refine Finset.sum_congr rfl ?_
      intro i _; rw [pow_mul]
    -- Conjugate: conj(P.eval(ω^k)) = ∑ j, P.coeff j * star(ω^(k*j))
    have hexpand_conj : ∀ k, (starRingEnd ℂ) (P.eval (ω ^ k)) =
        ∑ j ∈ Finset.range N, P.coeff j * (starRingEnd ℂ) (ω ^ (k * j)) := by
      intro k
      rw [hexpand k, map_sum]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [map_mul, hcoeff_conj j hj]
    -- Rewrite each summand: expand P and its conjugate, distribute as double sum.
    rw [show (∑ k ∈ Finset.range N, P.eval (ω ^ k) * (starRingEnd ℂ) (P.eval (ω ^ k))) =
        ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (P.coeff i * ω ^ (k * i)) * (P.coeff j * (starRingEnd ℂ) (ω ^ (k * j))) from
      Finset.sum_congr rfl fun k _ => by
        rw [hexpand_conj k, hexpand k, Finset.sum_mul_sum]]
    -- Use calc with named sum_comm applications.
    calc ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (P.coeff i * ω ^ (k * i)) * (P.coeff j * (starRingEnd ℂ) (ω ^ (k * j)))
        = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            (P.coeff i * ω ^ (k * i)) * (P.coeff j * (starRingEnd ℂ) (ω ^ (k * j))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Finset.sum_comm
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (P.coeff i * P.coeff j) *
            (∑ k ∈ Finset.range N, ω ^ (k * i) * (starRingEnd ℂ) (ω ^ (k * j))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (P.coeff i * P.coeff j) * (if i = j then (N : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
          rw [hortho_pair i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
      _ = ∑ i ∈ Finset.range N, (P.coeff i * P.coeff i) * (N : ℂ) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          simp only [mul_ite, mul_zero]
          rw [Finset.sum_ite_eq (Finset.range N) i
                (fun j => P.coeff i * P.coeff j * (N : ℂ)), if_pos hi]
      _ = (N : ℂ) * ∑ i ∈ Finset.range N, ((‖P.coeff i‖ ^ 2 : ℝ) : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hnorm_sq_cast (P.coeff i), hcoeff_conj i hi]
          ring
      _ = (N : ℂ) * ((∑ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 : ℝ) : ℂ) := by
          rw [show ((∑ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 : ℝ) : ℂ) =
                  ∑ i ∈ Finset.range N, ((‖P.coeff i‖ ^ 2 : ℝ) : ℂ) from by push_cast; rfl]
      _ = (N : ℂ) ^ 2 := by
          rw [hsum_coeff_sq]; push_cast; ring
  -- Pigeonhole: some k₀ has ‖P.eval (ω^{k₀})‖² ≥ N.
  have hexists : ∃ k₀ ∈ Finset.range N, ‖P.eval (ω ^ k₀)‖ ^ 2 ≥ (N : ℝ) := by
    by_contra hlt
    push_neg at hlt
    have hsum_lt : ∑ k ∈ Finset.range N, ‖P.eval (ω ^ k)‖ ^ 2 < N * (N : ℝ) := by
      calc ∑ k ∈ Finset.range N, ‖P.eval (ω ^ k)‖ ^ 2
          < ∑ _k ∈ Finset.range N, (N : ℝ) := by
            apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hNpos.ne')
            intro k hk
            exact hlt k hk
        _ = N * (N : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum_eval_sq] at hsum_lt
    have : (N : ℝ) ^ 2 < (N : ℝ) ^ 2 := by linarith [sq (N : ℝ)]
    exact lt_irrefl _ this
  obtain ⟨k₀, hk₀_mem, hk₀_bound⟩ := hexists
  -- ω^{k₀} lies on the unit sphere.
  have hω_pow_sphere : ω ^ k₀ ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_pow, hω_norm, one_pow]
  -- Conclude: √(N) ≤ ‖P.eval (ω^{k₀})‖ ≤ ⨆ ‖P.eval z‖.
  have hsqrt_le : Real.sqrt (N : ℝ) ≤ ‖P.eval (ω ^ k₀)‖ := by
    rw [show ‖P.eval (ω ^ k₀)‖ = Real.sqrt (‖P.eval (ω ^ k₀)‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hk₀_bound
  have hle_sup :
      ‖P.eval (ω ^ k₀)‖ ≤ ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ := by
    -- The sup is bounded: for ‖z‖ ≤ 1, ‖P.eval z‖ ≤ ∑ ‖aᵢ‖ ≤ N.
    have hbdd : BddAbove (Set.range fun z : Metric.sphere (0 : ℂ) 1 => ‖P.eval (z : ℂ)‖) := by
      refine ⟨(N : ℝ), ?_⟩
      rintro _ ⟨⟨z, hz⟩, rfl⟩
      have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hdeg' : P.natDegree < N := by rw [hN, hdeg]; exact Nat.lt_succ_self n
      calc ‖P.eval z‖
          = ‖∑ i ∈ Finset.range N, P.coeff i * z ^ i‖ := by
            rw [Polynomial.eval_eq_sum_range' hdeg']
        _ ≤ ∑ i ∈ Finset.range N, ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
        _ = ∑ i ∈ Finset.range N, ‖P.coeff i‖ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [norm_mul, norm_pow, hz1, one_pow, mul_one]
        _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' : i ≤ n := by
              have := Finset.mem_range.mp hi
              omega
            have := hcoeff_sq i hi'
            nlinarith [norm_nonneg (P.coeff i)]
        _ = (N : ℝ) := by simp
    exact le_ciSup_of_le hbdd ⟨ω ^ k₀, hω_pow_sphere⟩ le_rfl
  calc Real.sqrt ((n : ℝ) + 1)
      = Real.sqrt (N : ℝ) := by push_cast [hN]; ring_nf
    _ ≤ ‖P.eval (ω ^ k₀)‖ := hsqrt_le
    _ ≤ _ := hle_sup

end Erdos1150
