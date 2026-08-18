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
# Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$)

The ratio $\zeta(4n)/\zeta(2n)^2$ for $n \ge 1$ is the rational number
$$ Q_n = -2 \frac{B_{4n}}{B_{2n}^2 \binom{4n}{2n}} $$
where $B_k$ is the $k$-th Bernoulli number. The sequence $a(n)$ is the numerator of $Q_n$,
with $a(0)$ defined as $2$.

*References:*
- [A114362](https://oeis.org/A114362)
-/

namespace OeisA114362

open scoped Nat Real
open Filter
open Complex

/--
The primary defining sequence `a`.
Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then
    2
  else
    let b4n : ℚ := bernoulli (4 * n)
    let b2n : ℚ := bernoulli (2 * n)
    let binomQn : ℚ := ↑(Nat.choose (4 * n) (2 * n))
    let qN : ℚ := -2 * b4n / (b2n * b2n * binomQn)
    qN.num.natAbs

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by
  congr

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  simp_all [a]
  norm_num only [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four, bernoulli'_two, Nat.choose]

@[category test, AMS 11]
theorem a_2 : a 2 = 6 := by
  delta a
  norm_num +decide
    [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_eq_zero_of_odd, Int.natAbs_eq_iff, Nat.choose]
  rw [bernoulli'_def]
  have α := sum_bernoulli'
  norm_num only
    [←eq_sub_of_add_eq' (α _ ▸ Finset.sum_range_succ _ _).symm ▸ mul_div_cancel_left₀ _,
      Finset.sum_range_succ, or_false, or_true, Nat.choose]

@[category test, AMS 11]
theorem a_3 : a 3 = 691 := by
  delta and a
  norm_num [bernoulli_eq_bernoulli'_of_ne_one, two_mul, Nat.cast_choose]
  rw [bernoulli'_def, bernoulli'_def]
  have := sum_bernoulli'
  have R M := this (M+1) ▸ Finset.sum_range_succ _ _
  norm_num only
    [Nat.choose, ←sub_eq_of_eq_add' (R _) ▸ mul_div_cancel_left₀ _, Finset.sum_range_succ]

/--
Conjecture: if an integer $n > 1$ is odd, then $\zeta(2n)/\zeta(n)^2$ is irrational.
Cf. W. Kohnen (link) and my conjecture in A348829. - Thomas Ordowski, Jan 05 2022
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn_gt_one : 1 < n) (hn_odd : Odd n) :
    Irrational ((riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re) := by
  sorry

/-- `t n` is used in the second conjecture. -/
noncomputable def t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

/-
### Auxiliary development for `conjecture2`

The strategy is the explicit Euler-product route: `ζ(m) = lim_N ∏_{p < N} (1 - p^{-m})⁻¹`
(mathlib's `riemannZeta_eulerProduct`), transported to `ℝ` by taking real parts, so that
`t n = lim_N ∏_{p < N} (1 - p^{-n})/(1 + p^{-n})`. Peeling off the primes `2, 3, 5, 7` from
this product and bounding the tail over primes `≥ 11` by an explicit elementary comparison
`∑_{k ≥ 11} k^{-n} ≤ 12 · 11^{-n}` (for `n ≥ 2`) yields a two-sided bound on `t n` around
`Q4 n := ∏_{p ∈ {2,3,5,7}} (1 - p^{-n})/(1 + p^{-n})`; the proof then finishes with explicit
rational-function algebra comparing `(1 - Q4 n)/(1 + Q4 n)` to `2^{-n} + 3^{-n} + 5^{-n} + 7^{-n}`.
-/

section OeisA114362Aux

open Finset Filter
open scoped Topology

set_option maxHeartbeats 1600000

/- #### Elementary helpers -/

@[category API, AMS 11]
private lemma inv_pow_pos {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : 0 < 1 / ((p : ℝ) ^ n) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact div_pos one_pos (pow_pos (by linarith) n)

@[category API, AMS 11]
private lemma inv_pow_lt_one {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    1 / ((p : ℝ) ^ n) < 1 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (1 : ℝ) < (p : ℝ) ^ n := one_lt_pow₀ (by linarith) (by omega)
  rw [div_lt_one (by linarith)]
  linarith

@[category API, AMS 11]
private lemma one_div_pow_mul (n : ℕ) (u v : ℝ) : (1 / u ^ n) * (1 / v ^ n) = 1 / (u * v) ^ n := by
  rw [mul_pow, div_mul_div_comm, one_mul]

/- #### The finite tail estimate `∑_{k=11}^{N-1} k^{-n} ≤ 12 · 11^{-n}` -/

@[category API, AMS 11]
private lemma tail_sq (N : ℕ) (hN : 12 ≤ N) :
    ∑ k ∈ Finset.Ico 12 N, 1 / ((k : ℝ) ^ 2) ≤ 1 / 11 - 1 / ((N : ℝ) - 1) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN]
    have hN' : (12 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : 1 / ((N : ℝ) ^ 2) ≤ 1 / ((N : ℝ) - 1) - 1 / (N : ℝ) := by
      rw [div_sub_div _ _ (by linarith) (by linarith),
        div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    have hcast : ((N : ℝ) + 1) - 1 = (N : ℝ) := by ring
    push_cast
    rw [hcast]
    linarith

@[category API, AMS 11]
private lemma tail_pow (n : ℕ) (hn : 2 ≤ n) (N : ℕ) :
    ∑ k ∈ Finset.Ico 11 N, 1 / ((k : ℝ) ^ n) ≤ 12 / (11 : ℝ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rcases lt_or_ge N 12 with hN | hN
  · have hemp : Finset.Ico 11 N = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    positivity
  · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 11 < N)]
    have hb : ∀ k ∈ Finset.Ico 12 N,
        1 / ((k : ℝ) ^ (m + 2)) ≤ (121 / (11 : ℝ) ^ (m + 2)) * (1 / (k : ℝ) ^ 2) := by
      intro k hk
      have hk12 : 12 ≤ k := (Finset.mem_Ico.mp hk).1
      have hkR : (12 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk12
      have h11 : ((11 : ℝ)) ^ m ≤ (k : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by linarith) m
      have e1 : (121 : ℝ) / (11 : ℝ) ^ (m + 2) * (1 / (k : ℝ) ^ 2)
          = 1 / ((11 : ℝ) ^ m * (k : ℝ) ^ 2) := by
        rw [pow_add]
        have h1 : ((11 : ℝ)) ^ m ≠ 0 := by positivity
        have h2 : ((k : ℝ)) ^ 2 ≠ 0 := by positivity
        field_simp
        ring
      have e2 : 1 / ((k : ℝ) ^ (m + 2)) = 1 / ((k : ℝ) ^ m * (k : ℝ) ^ 2) := by rw [pow_add]
      rw [e1, e2]
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact mul_le_mul_of_nonneg_right h11 (by positivity)
    have hsum : ∑ k ∈ Finset.Ico 12 N, 1 / ((k : ℝ) ^ (m + 2)) ≤ 11 / (11 : ℝ) ^ (m + 2) := by
      have hNR : (12 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      calc ∑ k ∈ Finset.Ico 12 N, 1 / ((k : ℝ) ^ (m + 2))
          ≤ ∑ k ∈ Finset.Ico 12 N, (121 / (11 : ℝ) ^ (m + 2)) * (1 / (k : ℝ) ^ 2) :=
            Finset.sum_le_sum hb
        _ = (121 / (11 : ℝ) ^ (m + 2)) * ∑ k ∈ Finset.Ico 12 N, (1 / (k : ℝ) ^ 2) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (121 / (11 : ℝ) ^ (m + 2)) * (1 / 11) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h := tail_sq N hN
            have hpos : (0 : ℝ) < 1 / ((N : ℝ) - 1) := by
              apply div_pos one_pos; linarith
            linarith
        _ = 11 / (11 : ℝ) ^ (m + 2) := by ring
    have hcast : ((11 : ℕ) : ℝ) = (11 : ℝ) := by norm_num
    rw [hcast]
    have harith : (1 : ℝ) / (11 : ℝ) ^ (m + 2) + 11 / (11 : ℝ) ^ (m + 2)
        = 12 / (11 : ℝ) ^ (m + 2) := by ring
    linarith

/- #### The finite product-versus-sum inequality -/

@[category API, AMS 11]
private lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ 1) →
      1 - ∑ i ∈ s, (1 - f i) ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.cons_induction with
  | empty => intro _ _; simp
  | cons a s ha ih =>
    intro h0 h1
    rw [Finset.sum_cons, Finset.prod_cons]
    have hmem : a ∈ Finset.cons a s ha := by simp
    have hfa0 : 0 ≤ f a := h0 a hmem
    have hfa1 : f a ≤ 1 := h1 a hmem
    have ih' := ih (fun i hi => h0 i (by simp [hi])) (fun i hi => h1 i (by simp [hi]))
    have hs : 0 ≤ ∑ i ∈ s, (1 - f i) :=
      Finset.sum_nonneg fun i hi => by have := h1 i (by simp [hi]); linarith
    nlinarith [mul_le_mul_of_nonneg_left ih' hfa0, mul_nonneg hs (sub_nonneg.2 hfa1)]

/- #### Real partial Euler products -/

/-- Partial Euler product `∏_{p < N} (1 - p^{-m})⁻¹`, as a real number. -/
private noncomputable def EP (m N : ℕ) : ℝ := ∏ p ∈ Nat.primesBelow N, (1 - 1 / (p : ℝ) ^ m)⁻¹

@[category API, AMS 11]
private lemma tendsto_EP (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (EP m) atTop (𝓝 (riemannZeta (m : ℂ)).re) := by
  have hs : 1 < ((m : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast lt_of_lt_of_le one_lt_two hm
  have h := riemannZeta_eulerProduct hs
  have key : ∀ N : ℕ, ((EP m N : ℝ) : ℂ)
      = ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-(m : ℂ)))⁻¹ := by
    intro N
    rw [EP, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    ring
  have h2 : Tendsto (fun N : ℕ ↦ ((EP m N : ℝ) : ℂ)) atTop (𝓝 (riemannZeta (m : ℂ))) := by
    simpa only [key] using h
  have h3 : Tendsto (fun N : ℕ ↦ (((EP m N : ℝ) : ℂ)).re) atTop (𝓝 (riemannZeta (m : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp h2
  simpa only [Complex.ofReal_re] using h3

@[category API, AMS 11]
private lemma one_le_EP (m N : ℕ) (hm : 1 ≤ m) : 1 ≤ EP m N := by
  have h : ∀ p ∈ Nat.primesBelow N, (1 : ℝ) ≤ (1 - 1 / (p : ℝ) ^ m)⁻¹ := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have h2 : 2 ≤ p := hpp.two_le
    have hx0 : 0 < 1 / ((p : ℝ) ^ m) := inv_pow_pos h2 m
    have hx1 : 1 / ((p : ℝ) ^ m) < 1 := inv_pow_lt_one h2 hm
    rw [le_inv_comm₀ (by norm_num) (by linarith)]
    linarith
  calc (1 : ℝ) = ∏ _p ∈ Nat.primesBelow N, (1 : ℝ) := by simp
    _ ≤ EP m N := Finset.prod_le_prod (fun i _ => zero_le_one) h

@[category API, AMS 11]
private lemma one_le_zeta_re (m : ℕ) (hm : 2 ≤ m) : 1 ≤ (riemannZeta (m : ℂ)).re :=
  ge_of_tendsto' (tendsto_EP m hm) (fun N => one_le_EP m N (by omega))

/- #### `t n` as a limit of finite products of `(1 - p^{-n})/(1 + p^{-n})` -/

/-- `qq n p = (1 - p^{-n}) / (1 + p^{-n})`. -/
private noncomputable def qq (n p : ℕ) : ℝ := (1 - 1 / (p : ℝ) ^ n) / (1 + 1 / (p : ℝ) ^ n)

@[category API, AMS 11]
private lemma qq_pos {n p : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) : 0 < qq n p := by
  have hx0 : 0 < 1 / ((p : ℝ) ^ n) := inv_pow_pos hp n
  have hx1 : 1 / ((p : ℝ) ^ n) < 1 := inv_pow_lt_one hp hn
  rw [qq]
  apply div_pos <;> linarith

@[category API, AMS 11]
private lemma qq_lt_one {n p : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) : qq n p < 1 := by
  have hx0 : 0 < 1 / ((p : ℝ) ^ n) := inv_pow_pos hp n
  have hx1 : 1 / ((p : ℝ) ^ n) < 1 := inv_pow_lt_one hp hn
  rw [qq, div_lt_one (by linarith)]
  linarith

@[category API, AMS 11]
private lemma one_sub_qq_le {n p : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) :
    1 - qq n p ≤ 2 * (1 / (p : ℝ) ^ n) := by
  have hx0 : 0 < 1 / ((p : ℝ) ^ n) := inv_pow_pos hp n
  have hx1 : 1 / ((p : ℝ) ^ n) < 1 := inv_pow_lt_one hp hn
  have hd : (0 : ℝ) < 1 + 1 / ((p : ℝ) ^ n) := by linarith
  have key : 1 - qq n p = 2 * (1 / (p : ℝ) ^ n) / (1 + 1 / (p : ℝ) ^ n) := by
    rw [qq, eq_div_iff (ne_of_gt hd), sub_mul, one_mul,
      div_mul_cancel₀ _ (ne_of_gt hd)]
    ring
  rw [key, div_le_iff₀ hd]
  nlinarith

@[category API, AMS 11]
private lemma tendsto_prod_qq (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun N ↦ ∏ p ∈ Nat.primesBelow N, qq n p) atTop (𝓝 (t n)) := by
  have h1 := tendsto_EP n hn
  have h2 := tendsto_EP (2 * n) (by omega)
  have hz : ((2 * n : ℕ) : ℂ) = 2 * (n : ℂ) := by push_cast; ring
  rw [hz] at h2
  have hZ1 : (1 : ℝ) ≤ (riemannZeta (n : ℂ)).re := one_le_zeta_re n hn
  have hne : ((riemannZeta (n : ℂ)).re) ^ 2 ≠ 0 := by positivity
  have hdiv := h2.div (h1.pow 2) hne
  have key : ∀ N : ℕ, EP (2 * n) N / (EP n N) ^ 2 = ∏ p ∈ Nat.primesBelow N, qq n p := by
    intro N
    rw [EP, EP, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hx0 : 0 < 1 / ((p : ℝ) ^ n) := inv_pow_pos hp2 n
    have hx1 : 1 / ((p : ℝ) ^ n) < 1 := inv_pow_lt_one hp2 (by omega)
    have hsq : (1 : ℝ) / (p : ℝ) ^ (2 * n) = (1 / (p : ℝ) ^ n) ^ 2 := by
      rw [div_pow, one_pow, mul_comm, pow_mul]
    rw [hsq, qq]
    have hfac : (1 : ℝ) - (1 / (p : ℝ) ^ n) ^ 2
        = (1 - 1 / (p : ℝ) ^ n) * (1 + 1 / (p : ℝ) ^ n) := by ring
    rw [hfac]
    have hA : (1 : ℝ) - 1 / (p : ℝ) ^ n ≠ 0 := by linarith
    have hB : (1 : ℝ) + 1 / (p : ℝ) ^ n ≠ 0 := by linarith
    field_simp
  have : (fun N ↦ ∏ p ∈ Nat.primesBelow N, qq n p)
      = fun N ↦ EP (2 * n) N / (EP n N) ^ 2 := by
    funext N; rw [key]
  rw [this]
  exact hdiv

/- #### Peeling off the primes 2, 3, 5, 7 -/

/-- `Q4 n = ∏_{p ∈ {2,3,5,7}} (1 - p^{-n})/(1 + p^{-n})`. -/
private noncomputable def Q4 (n : ℕ) : ℝ := qq n 2 * qq n 3 * qq n 5 * qq n 7

@[category API, AMS 11]
private lemma prod_four (n : ℕ) : ∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), qq n p = Q4 n := by
  rw [show ({2, 3, 5, 7} : Finset ℕ) = insert 2 (insert 3 (insert 5 {7})) from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, Q4]
  ring

@[category API, AMS 11]
private lemma Q4_pos (n : ℕ) (hn : 1 ≤ n) : 0 < Q4 n := by
  rw [Q4]
  exact mul_pos (mul_pos (mul_pos (qq_pos (by norm_num) hn) (qq_pos (by norm_num) hn))
    (qq_pos (by norm_num) hn)) (qq_pos (by norm_num) hn)

@[category API, AMS 11]
private lemma Q4_lt_one (n : ℕ) (hn : 1 ≤ n) : Q4 n < 1 := by
  have h2 := qq_pos (n := n) (p := 2) (by norm_num) hn
  have h3 := qq_pos (n := n) (p := 3) (by norm_num) hn
  have h5 := qq_pos (n := n) (p := 5) (by norm_num) hn
  have h7 := qq_pos (n := n) (p := 7) (by norm_num) hn
  have k2 := qq_lt_one (n := n) (p := 2) (by norm_num) hn
  have k3 := qq_lt_one (n := n) (p := 3) (by norm_num) hn
  have k5 := qq_lt_one (n := n) (p := 5) (by norm_num) hn
  have k7 := qq_lt_one (n := n) (p := 7) (by norm_num) hn
  have p23 : 0 < qq n 2 * qq n 3 := mul_pos h2 h3
  have s1 : qq n 2 * qq n 3 < 1 := by nlinarith [mul_pos (sub_pos.2 k2) h3]
  have p235 : 0 < qq n 2 * qq n 3 * qq n 5 := mul_pos p23 h5
  have s2 : qq n 2 * qq n 3 * qq n 5 < 1 := by nlinarith [mul_pos (sub_pos.2 s1) h5]
  rw [Q4]
  nlinarith [mul_pos (sub_pos.2 s2) h7]

@[category API, AMS 11]
private lemma four_subset (N : ℕ) (hN : 8 ≤ N) : ({2, 3, 5, 7} : Finset ℕ) ⊆ Nat.primesBelow N := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rw [Nat.mem_primesBelow]
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨by omega, by norm_num⟩
  · exact ⟨by omega, by norm_num⟩
  · exact ⟨by omega, by norm_num⟩
  · exact ⟨by omega, by norm_num⟩

@[category API, AMS 11]
private lemma sdiff_subset_Ico (N : ℕ) :
    Nat.primesBelow N \ ({2, 3, 5, 7} : Finset ℕ) ⊆ Finset.Ico 11 N := by
  intro p hp
  rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hp
  obtain ⟨⟨hlt, hpr⟩, hnot⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
  rw [Finset.mem_Ico]
  refine ⟨?_, hlt⟩
  by_contra hcon
  rw [Nat.not_le] at hcon
  interval_cases p <;> revert hpr hnot <;> decide

/-- The tail product over primes `≥ 11` is between `1 - 24·11^{-n}` and `1`. -/
@[category API, AMS 11]
private lemma tail_prod_bounds (n N : ℕ) (hn : 2 ≤ n) :
    (0 < ∏ p ∈ Nat.primesBelow N \ ({2, 3, 5, 7} : Finset ℕ), qq n p) ∧
    (∏ p ∈ Nat.primesBelow N \ ({2, 3, 5, 7} : Finset ℕ), qq n p ≤ 1) ∧
    (1 - 24 * (1 / (11 : ℝ) ^ n) ≤
      ∏ p ∈ Nat.primesBelow N \ ({2, 3, 5, 7} : Finset ℕ), qq n p) := by
  set s := Nat.primesBelow N \ ({2, 3, 5, 7} : Finset ℕ) with hs
  have hmem : ∀ p ∈ s, 2 ≤ p := by
    intro p hp
    rw [hs, Finset.mem_sdiff, Nat.mem_primesBelow] at hp
    exact hp.1.2.two_le
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => qq_pos (hmem p hp) (by omega)
  · exact Finset.prod_le_one (fun p hp => (qq_pos (hmem p hp) (by omega)).le)
      (fun p hp => (qq_lt_one (hmem p hp) (by omega)).le)
  · have hkey := one_sub_sum_le_prod s (qq n)
      (fun p hp => (qq_pos (hmem p hp) (by omega)).le)
      (fun p hp => (qq_lt_one (hmem p hp) (by omega)).le)
    have hsum : ∑ p ∈ s, (1 - qq n p) ≤ 24 * (1 / (11 : ℝ) ^ n) := by
      calc ∑ p ∈ s, (1 - qq n p)
          ≤ ∑ p ∈ s, 2 * (1 / (p : ℝ) ^ n) :=
            Finset.sum_le_sum fun p hp => one_sub_qq_le (hmem p hp) (by omega)
        _ = 2 * ∑ p ∈ s, (1 / (p : ℝ) ^ n) := (Finset.mul_sum _ _ _).symm
        _ ≤ 2 * ∑ k ∈ Finset.Ico 11 N, (1 / (k : ℝ) ^ n) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            refine Finset.sum_le_sum_of_subset_of_nonneg (sdiff_subset_Ico N) ?_
            intro k hk _
            have : 11 ≤ k := (Finset.mem_Ico.mp hk).1
            exact (inv_pow_pos (by omega) n).le
        _ ≤ 2 * (12 / (11 : ℝ) ^ n) := by
            exact mul_le_mul_of_nonneg_left (tail_pow n hn N) (by norm_num)
        _ = 24 * (1 / (11 : ℝ) ^ n) := by ring
    linarith

@[category API, AMS 11]
private lemma t_upper (n : ℕ) (hn : 2 ≤ n) : t n ≤ Q4 n := by
  refine le_of_tendsto (tendsto_prod_qq n hn) ?_
  filter_upwards [eventually_ge_atTop 8] with N hN
  classical
  rw [← Finset.prod_sdiff (four_subset N hN), prod_four]
  obtain ⟨hp0, hp1, _⟩ := tail_prod_bounds n N hn
  have hQ := Q4_pos n (by omega)
  nlinarith

@[category API, AMS 11]
private lemma t_lower (n : ℕ) (hn : 2 ≤ n) : Q4 n * (1 - 24 * (1 / (11 : ℝ) ^ n)) ≤ t n := by
  refine ge_of_tendsto (tendsto_prod_qq n hn) ?_
  filter_upwards [eventually_ge_atTop 8] with N hN
  classical
  rw [← Finset.prod_sdiff (four_subset N hN), prod_four]
  obtain ⟨hp0, hp1, hp2⟩ := tail_prod_bounds n N hn
  have hQ := Q4_pos n (by omega)
  nlinarith

/- #### The algebraic core -/

/-- Monotone-decreasing comparison for `u ↦ (1-u)/(1+u)`, plus the perturbation bound. -/
@[category API, AMS 11]
private lemma y_bounds {P T e : ℝ} (hP0 : 0 < P) (hP1 : P < 1) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 5)
    (hTP : T ≤ P) (hPT : P * (1 - e) ≤ T) :
    (1 - P) / (1 + P) ≤ (1 - T) / (1 + T) ∧
      (1 - T) / (1 + T) ≤ (1 - P) / (1 + P) + e := by
  have hT0 : 0 < T := by nlinarith
  have hd1 : (0 : ℝ) < 1 + P := by linarith
  have hd2 : (0 : ℝ) < 1 + T := by linarith
  constructor
  · rw [div_le_div_iff₀ hd1 hd2]
    nlinarith
  · rw [div_add' _ _ _ (ne_of_gt hd1), div_le_div_iff₀ hd2 hd1]
    nlinarith [mul_nonneg he0 (by nlinarith : (0:ℝ) ≤ 1 - P + T + P * T)]

/-- `(1 - P)/(1 + P)` with `P = ∏ (1-x)/(1+x)` is within an explicit distance of `∑ x`. -/
@[category API, AMS 11]
private lemma abs_A_sub_S (a b c d P : ℝ)
    (hd : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a) (ha4 : a ≤ 1 / 4)
    (hP : P = ((1 - a) / (1 + a)) * ((1 - b) / (1 + b)) * ((1 - c) / (1 + c)) *
      ((1 - d) / (1 + d))) :
    |(1 - P) / (1 + P) - (a + b + c + d)|
      ≤ 24 * (a ^ 2 * b) + 4 * (a * b * c) + 4 * (a ^ 2 * b * c * d) := by
  have hc : 0 < c := lt_of_lt_of_le hd hdc
  have hb : 0 < b := lt_of_lt_of_le hc hcb
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hb4 : b ≤ 1 / 4 := le_trans hba ha4
  have hc4 : c ≤ 1 / 4 := le_trans hcb hb4
  have hd4 : d ≤ 1 / 4 := le_trans hdc hc4
  have hDpos : (0 : ℝ) < (1 + a) * (1 + b) * (1 + c) * (1 + d) := by positivity
  have hNpos : (0 : ℝ) < (1 - a) * (1 - b) * (1 - c) * (1 - d) := by
    apply mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)
  have hPeq : P = ((1 - a) * (1 - b) * (1 - c) * (1 - d)) /
      ((1 + a) * (1 + b) * (1 + c) * (1 + d)) := by
    rw [hP]; field_simp
  -- the key rational identity
  have hDN2 : (0 : ℝ) < ((1 + a) * (1 + b) * (1 + c) * (1 + d)) +
      ((1 - a) * (1 - b) * (1 - c) * (1 - d)) := by linarith
  have h1P : 1 - P = (((1 + a) * (1 + b) * (1 + c) * (1 + d)) -
      ((1 - a) * (1 - b) * (1 - c) * (1 - d))) / ((1 + a) * (1 + b) * (1 + c) * (1 + d)) := by
    rw [hPeq]; field_simp
  have h2P : 1 + P = (((1 + a) * (1 + b) * (1 + c) * (1 + d)) +
      ((1 - a) * (1 - b) * (1 - c) * (1 - d))) / ((1 + a) * (1 + b) * (1 + c) * (1 + d)) := by
    rw [hPeq]; field_simp
  have hquot : (1 - P) / (1 + P) =
      (((1 + a) * (1 + b) * (1 + c) * (1 + d)) - ((1 - a) * (1 - b) * (1 - c) * (1 - d))) /
      (((1 + a) * (1 + b) * (1 + c) * (1 + d)) + ((1 - a) * (1 - b) * (1 - c) * (1 - d))) := by
    rw [h1P, h2P, div_div_div_cancel_right₀ (ne_of_gt hDpos)]
  have hnum : ((1 + a) * (1 + b) * (1 + c) * (1 + d)) - ((1 - a) * (1 - b) * (1 - c) * (1 - d))
      = 2 * ((a + b + c + d) + (a * b * c + a * b * d + a * c * d + b * c * d)) := by ring
  have hden : ((1 + a) * (1 + b) * (1 + c) * (1 + d)) + ((1 - a) * (1 - b) * (1 - c) * (1 - d))
      = 2 * (1 + (a * b + a * c + a * d + b * c + b * d + c * d) + a * b * c * d) := by ring
  rw [hquot, hnum, hden, mul_div_mul_left _ _ (two_ne_zero)]
  -- now pure symmetric-function algebra
  have hE2 : (0 : ℝ) ≤ a * b + a * c + a * d + b * c + b * d + c * d := by positivity
  have hE4 : (0 : ℝ) ≤ a * b * c * d := by positivity
  have hDen1 : (1 : ℝ) ≤ 1 + (a * b + a * c + a * d + b * c + b * d + c * d) + a * b * c * d := by
    linarith
  have hDenPos : (0 : ℝ) < 1 + (a * b + a * c + a * d + b * c + b * d + c * d) + a * b * c * d := by
    linarith
  have hW : ((a + b + c + d) + (a * b * c + a * b * d + a * c * d + b * c * d)) /
      (1 + (a * b + a * c + a * d + b * c + b * d + c * d) + a * b * c * d) - (a + b + c + d)
      = ((a * b * c + a * b * d + a * c * d + b * c * d)
          - (a + b + c + d) * (a * b + a * c + a * d + b * c + b * d + c * d)
          - (a + b + c + d) * (a * b * c * d)) /
        (1 + (a * b + a * c + a * d + b * c + b * d + c * d) + a * b * c * d) := by
    field_simp
    ring
  rw [hW, abs_div, abs_of_pos hDenPos, div_le_iff₀ hDenPos]
  -- bounds on the elementary symmetric functions
  have he1 : a + b + c + d ≤ 4 * a := by linarith
  have he1nn : (0 : ℝ) ≤ a + b + c + d := by linarith
  have he2 : a * b + a * c + a * d + b * c + b * d + c * d ≤ 6 * (a * b) := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.2 hcb), mul_nonneg ha.le (sub_nonneg.2 (hdc.trans hcb)),
      mul_nonneg hb.le (sub_nonneg.2 (hcb.trans hba)),
      mul_nonneg hb.le (sub_nonneg.2 ((hdc.trans hcb).trans hba)),
      mul_nonneg hb.le (sub_nonneg.2 hdc), mul_nonneg hc.le (sub_nonneg.2 hba)]
  have he3 : a * b * c + a * b * d + a * c * d + b * c * d ≤ 4 * (a * b * c) := by
    nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) (sub_nonneg.2 hdc),
      mul_nonneg (mul_nonneg ha.le hc.le) (sub_nonneg.2 (hdc.trans hcb)),
      mul_nonneg (mul_nonneg hb.le hc.le) (sub_nonneg.2 (((hdc.trans hcb).trans hba)))]
  have he3nn : (0 : ℝ) ≤ a * b * c + a * b * d + a * c * d + b * c * d := by positivity
  have hprod12 : (a + b + c + d) * (a * b + a * c + a * d + b * c + b * d + c * d)
      ≤ 24 * (a ^ 2 * b) := by
    calc (a + b + c + d) * (a * b + a * c + a * d + b * c + b * d + c * d)
        ≤ (4 * a) * (6 * (a * b)) := by
          apply mul_le_mul he1 he2 hE2 (by linarith)
      _ = 24 * (a ^ 2 * b) := by ring
  have hprod14 : (a + b + c + d) * (a * b * c * d) ≤ 4 * (a ^ 2 * b * c * d) := by
    calc (a + b + c + d) * (a * b * c * d) ≤ (4 * a) * (a * b * c * d) := by
          apply mul_le_mul_of_nonneg_right he1 (by positivity)
      _ = 4 * (a ^ 2 * b * c * d) := by ring
  have hprod12nn : (0 : ℝ) ≤ (a + b + c + d) * (a * b + a * c + a * d + b * c + b * d + c * d) := by
    positivity
  have hprod14nn : (0 : ℝ) ≤ (a + b + c + d) * (a * b * c * d) := by positivity
  have habs : |(a * b * c + a * b * d + a * c * d + b * c * d)
      - (a + b + c + d) * (a * b + a * c + a * d + b * c + b * d + c * d)
      - (a + b + c + d) * (a * b * c * d)|
      ≤ 24 * (a ^ 2 * b) + 4 * (a * b * c) + 4 * (a ^ 2 * b * c * d) := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  have hBnn : (0 : ℝ) ≤ 24 * (a ^ 2 * b) + 4 * (a * b * c) + 4 * (a ^ 2 * b * c * d) := by
    positivity
  nlinarith

/- #### The explicit bound -/

@[category API, AMS 11]
private lemma main_bound (n : ℕ) (hn : 2 ≤ n) :
    |(1 - t n) / (1 + t n) -
      (1 / (2 : ℝ) ^ n + 1 / (3 : ℝ) ^ n + 1 / (5 : ℝ) ^ n + 1 / (7 : ℝ) ^ n)|
      ≤ 56 * (1 / (11 : ℝ) ^ n) := by
  have hn1 : 1 ≤ n := by omega
  -- basic numeric facts about the four "x_p"
  have hpow : ∀ (r : ℝ), 1 ≤ r → (0:ℝ) < r ^ n := fun r hr => by positivity
  have h2 : (0 : ℝ) < 1 / (2 : ℝ) ^ n := by positivity
  have h3 : (0 : ℝ) < 1 / (3 : ℝ) ^ n := by positivity
  have h5 : (0 : ℝ) < 1 / (5 : ℝ) ^ n := by positivity
  have h7 : (0 : ℝ) < 1 / (7 : ℝ) ^ n := by positivity
  have hmono : ∀ (r s : ℝ), 0 < r → r ≤ s → 1 / s ^ n ≤ 1 / r ^ n := by
    intro r s hr hrs
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hr.le hrs n)
  have h32 : 1 / (3 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ n := hmono 2 3 (by norm_num) (by norm_num)
  have h53 : 1 / (5 : ℝ) ^ n ≤ 1 / (3 : ℝ) ^ n := hmono 3 5 (by norm_num) (by norm_num)
  have h75 : 1 / (7 : ℝ) ^ n ≤ 1 / (5 : ℝ) ^ n := hmono 5 7 (by norm_num) (by norm_num)
  have h2q : 1 / (2 : ℝ) ^ n ≤ 1 / 4 := by
    have : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
      calc (4:ℝ) = (2:ℝ)^2 := by norm_num
        _ ≤ (2:ℝ)^n := by
          apply pow_le_pow_right₀ (by norm_num) hn
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- identify Q4 n
  have hq2 : qq n 2 = (1 - 1 / (2 : ℝ) ^ n) / (1 + 1 / (2 : ℝ) ^ n) := by
    rw [qq]; norm_num
  have hq3 : qq n 3 = (1 - 1 / (3 : ℝ) ^ n) / (1 + 1 / (3 : ℝ) ^ n) := by
    rw [qq]; norm_num
  have hq5 : qq n 5 = (1 - 1 / (5 : ℝ) ^ n) / (1 + 1 / (5 : ℝ) ^ n) := by
    rw [qq]; norm_num
  have hq7 : qq n 7 = (1 - 1 / (7 : ℝ) ^ n) / (1 + 1 / (7 : ℝ) ^ n) := by
    rw [qq]; norm_num
  have hQ4 : Q4 n = ((1 - 1 / (2 : ℝ) ^ n) / (1 + 1 / (2 : ℝ) ^ n)) *
      ((1 - 1 / (3 : ℝ) ^ n) / (1 + 1 / (3 : ℝ) ^ n)) *
      ((1 - 1 / (5 : ℝ) ^ n) / (1 + 1 / (5 : ℝ) ^ n)) *
      ((1 - 1 / (7 : ℝ) ^ n) / (1 + 1 / (7 : ℝ) ^ n)) := by
    rw [Q4, hq2, hq3, hq5, hq7]
  -- the epsilon
  have h11 : (121 : ℝ) ≤ (11 : ℝ) ^ n := by
    calc (121:ℝ) = (11:ℝ)^2 := by norm_num
      _ ≤ (11:ℝ)^n := by apply pow_le_pow_right₀ (by norm_num) hn
  have h11pos : (0 : ℝ) < (11 : ℝ) ^ n := by positivity
  have heps0 : (0 : ℝ) ≤ 24 * (1 / (11 : ℝ) ^ n) := by positivity
  have heps1 : 24 * (1 / (11 : ℝ) ^ n) ≤ 1 / 5 := by
    rw [mul_one_div, div_le_div_iff₀ h11pos (by norm_num)]
    linarith
  -- the two-sided bound on t n
  have hQ0 : 0 < Q4 n := Q4_pos n hn1
  have hQ1 : Q4 n < 1 := Q4_lt_one n hn1
  have hup := t_upper n hn
  have hlo := t_lower n hn
  obtain ⟨hy1, hy2⟩ := y_bounds (P := Q4 n) (T := t n) (e := 24 * (1 / (11 : ℝ) ^ n))
    hQ0 hQ1 heps0 heps1 hup hlo
  -- the four-prime defect
  have hAS := abs_A_sub_S (1 / (2 : ℝ) ^ n) (1 / (3 : ℝ) ^ n) (1 / (5 : ℝ) ^ n)
    (1 / (7 : ℝ) ^ n) (Q4 n) h7 h75 h53 h32 h2q hQ4
  -- convert the defect bound into a multiple of 11^{-n}
  have e12 : (1 / (2 : ℝ) ^ n) ^ 2 * (1 / (3 : ℝ) ^ n) = 1 / (12 : ℝ) ^ n := by
    rw [pow_two, one_div_pow_mul, one_div_pow_mul]
    norm_num
  have e30 : (1 / (2 : ℝ) ^ n) * (1 / (3 : ℝ) ^ n) * (1 / (5 : ℝ) ^ n) = 1 / (30 : ℝ) ^ n := by
    rw [one_div_pow_mul, one_div_pow_mul]
    norm_num
  have e420 : (1 / (2 : ℝ) ^ n) ^ 2 * (1 / (3 : ℝ) ^ n) * (1 / (5 : ℝ) ^ n) *
      (1 / (7 : ℝ) ^ n) = 1 / (420 : ℝ) ^ n := by
    rw [pow_two, one_div_pow_mul, one_div_pow_mul, one_div_pow_mul, one_div_pow_mul]
    norm_num
  have c12 : 1 / (12 : ℝ) ^ n ≤ 1 / (11 : ℝ) ^ n := hmono 11 12 (by norm_num) (by norm_num)
  have c30 : 1 / (30 : ℝ) ^ n ≤ 1 / (11 : ℝ) ^ n := hmono 11 30 (by norm_num) (by norm_num)
  have c420 : 1 / (420 : ℝ) ^ n ≤ 1 / (11 : ℝ) ^ n := hmono 11 420 (by norm_num) (by norm_num)
  rw [e420, e12, e30] at hAS
  -- combine
  have habs2 : |(1 - t n) / (1 + t n) - (1 - Q4 n) / (1 + Q4 n)| ≤ 24 * (1 / (11 : ℝ) ^ n) := by
    rw [abs_le]; constructor <;> linarith
  calc |(1 - t n) / (1 + t n) -
      (1 / (2 : ℝ) ^ n + 1 / (3 : ℝ) ^ n + 1 / (5 : ℝ) ^ n + 1 / (7 : ℝ) ^ n)|
      ≤ |(1 - t n) / (1 + t n) - (1 - Q4 n) / (1 + Q4 n)| +
        |(1 - Q4 n) / (1 + Q4 n) -
          (1 / (2 : ℝ) ^ n + 1 / (3 : ℝ) ^ n + 1 / (5 : ℝ) ^ n + 1 / (7 : ℝ) ^ n)| := by
        exact abs_sub_le _ _ _
    _ ≤ 24 * (1 / (11 : ℝ) ^ n) + (24 * (1 / (12 : ℝ) ^ n) + 4 * (1 / (30 : ℝ) ^ n) +
          4 * (1 / (420 : ℝ) ^ n)) := by
        exact add_le_add habs2 hAS
    _ ≤ 56 * (1 / (11 : ℝ) ^ n) := by linarith

end OeisA114362Aux

/--
Conjecture:
$\frac{1 - t(n)}{1 + t(n)} = \frac{1}{2^n} + \frac{1}{3^n} + \frac{1}{5^n} + \frac{1}{7^n} +
  O(\frac{1}{11^n})$,
where $t(n) = \zeta(2n)/\zeta(n)^2$. Cf. A348829. - Thomas Ordowski, Nov 13 2022
-/
@[category research solved, AMS 11]
theorem conjecture2 :
    (fun n : ℕ => (1 - t n) / (1 + t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨56, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (11:ℝ) ^ n)]
  exact main_bound n hn

end OeisA114362
