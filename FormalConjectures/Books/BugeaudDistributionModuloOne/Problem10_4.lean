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
# Bugeaud Collection of Conjectures and Open Questions: Spectrum of Sequence
*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Men73] Mendès France, Michel. "Les ensembles de Bésineau."
    Séminaire Delange-Pisot-Poitou 15.1 (1973): 1-6.
  - [Özc26] Özcan, Hikmet Burak. "The spectrum of $(\xi\alpha^n)$ can be uncountable."
    [arXiv:2609.07714](https://arxiv.org/abs/2609.07714) (2026).

## Counterexample

Problem 10.4 is false. Özcan [Özc26] proves that for every real $\alpha > 1$ there are
$2^{\aleph_0}$ reals $\xi > 0$ whose spectrum contains one and the same uncountable set.
The counterexample below is an independent, self-contained instance of this for the base
$\alpha = 64$, where the digits of $\xi$ can be prescribed directly.

For a bit sequence $u \in \{0, 1\}^{\mathbb{N}}$ put
$$\theta_u = \sum_{i \ge 0} (1 + u_i) \, 8^{-e(i)}, \qquad e(i) = 4^{i+1} + i + 6.$$
The map $u \mapsto \theta_u$ is injective with values in $(0, 1)$.

Split the indices into the blocks $[5 m_k, 6 m_k)$ with $m_k = 20 \cdot 8^k$; these are
pairwise disjoint. Block number $k = \langle L, c \rangle$, where $\langle \cdot, \cdot \rangle$
is the Cantor pairing, is reserved for the bit string $c$ of length $L$. On that block the
base-$64$ digits of $\xi$ are chosen so that $\{\xi 64^n\}$ shadows $\{n \theta\}$ for every
$\theta$ whose first $L$ bits are $c$. This is possible because one base-$64$ digit pins down
$\{\xi 64^n\}$ up to $2/64$, and because $k \le 4^{L+1}$ forces the block to sit far to the left
of the precision $8^{-e(L)}$ of the truncation of $\theta$, so that $n$ times the truncation
error stays below $1/512$ on the block.

Consequently $\{\xi 64^n - n \theta_u\} < 1/10$ for all $n$ in the block attached to the first
$L$ bits of $u$, for every $L$. That block is the last sixth of $[0, 6 m_k)$, so at the times
$N = 6 m_k - 6$ at most a proportion $5/6$ of the points $\{\xi 64^n - n\theta_u\}$ with $n < N$
lies in $[1/10, 1]$, whereas uniform distribution modulo one would force the proportion
$9/10$. Hence every irrational $\theta_u$ lies in the spectrum of $(\xi 64^n)$, and since
$\{\theta_u\}$ is uncountable the spectrum cannot be countable.
-/

@[expose] public section

namespace Bugeaud04

open scoped Topology

/--
The spectrum of a sequence $(x_n)_{n \ge 1}$ of real numbers is the set of
irrational real numbers $\theta \in (0, 1)$ such that the sequence
$(x_n - n\theta)_{n \ge 1}$ is not uniformly distributed modulo one.
-/
def Spectrum (x : ℕ → ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioo (0 : ℝ) 1 ∧ Irrational θ ∧
    ¬ IsEquidistributedModuloOne (fun n => x n - n * θ)}

/-! ### The blocks of indices

The $k$-th block is the interval of indices $[5 m_k, 6 m_k)$, where `scale k` is $m_k$.
-/

/-- The scale $m_k = 20 \cdot 8^k$ of the $k$-th block of indices. -/
private def scale (k : ℕ) : ℕ := 20 * 8 ^ k

@[category API, AMS 11]
private lemma twenty_le_scale (k : ℕ) : 20 ≤ scale k := by
  dsimp [scale]
  have : 1 ≤ 8 ^ k := Nat.one_le_pow k 8 (by omega)
  omega

@[category API, AMS 11]
private lemma add_twenty_le_scale (k : ℕ) : k + 20 ≤ scale k := by
  dsimp [scale]
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

@[category API, AMS 11]
private lemma scale_succ (k : ℕ) : scale (k + 1) = 8 * scale k := by
  dsimp [scale]
  ring

@[category API, AMS 11]
private lemma scale_mono {a b : ℕ} (h : a ≤ b) : scale a ≤ scale b :=
  Nat.mul_le_mul_left 20 (Nat.pow_le_pow_right (by omega) h)

/-- The blocks $[5 m_k, 6 m_k)$ are pairwise disjoint. -/
@[category API, AMS 11]
private lemma block_unique {k₁ k₂ n : ℕ}
    (h1 : 5 * scale k₁ ≤ n ∧ n < 6 * scale k₁)
    (h2 : 5 * scale k₂ ≤ n ∧ n < 6 * scale k₂) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
  · have hle : scale (k₁ + 1) ≤ scale k₂ := scale_mono hlt
    rw [scale_succ] at hle
    have := twenty_le_scale k₁
    omega
  · rfl
  · have hle : scale (k₂ + 1) ≤ scale k₁ := scale_mono hgt
    rw [scale_succ] at hle
    have := twenty_le_scale k₂
    omega

/-- The index of the block containing `n`, and `0` if `n` lies in no block. -/
private def blockIdx (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, if 5 * scale k ≤ n ∧ n < 6 * scale k then k else 0

@[category API, AMS 11]
private lemma blockIdx_eq_of_mem {k n : ℕ} (h1 : 5 * scale k ≤ n) (h2 : n < 6 * scale k) :
    blockIdx n = k := by
  dsimp [blockIdx]
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨h1, h2⟩]
  · intro j _ hj
    rw [if_neg]
    intro hj_mem
    exact hj (block_unique hj_mem ⟨h1, h2⟩)
  · intro hk_not_mem
    exfalso
    apply hk_not_mem
    rw [Finset.mem_range]
    have := add_twenty_le_scale k
    omega

/-! ### The uncountable family of frequencies -/

/-- An upper bound for the indices of the blocks reserved for bit strings of length `L`. -/
private def bound (L : ℕ) : ℕ := 4 ^ (L + 1)

/-- The exponent $e(L) = 4^{L+1} + L + 6$ used in the $L$-th term of $\theta_u$. -/
private def expo (L : ℕ) : ℕ := bound L + L + 6

@[category API, AMS 11]
private lemma bound_mono {a b : ℕ} (h : a ≤ b) : bound a ≤ bound b :=
  Nat.pow_le_pow_right (by omega) (by omega)

@[category API, AMS 11]
private lemma le_expo_add (L j : ℕ) : bound L + j + 6 ≤ expo (j + L) := by
  dsimp [expo]
  have := bound_mono (by omega : L ≤ j + L)
  omega

@[category API, AMS 11]
private lemma expo_add_succ_le (L j : ℕ) : expo L + j + 1 ≤ expo (j + L + 1) := by
  dsimp [expo]
  have : bound L < bound (j + L + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- The number whose binary digits are the first `L` bits of `u`. -/
private def code (u : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | L + 1 => 2 * code u L + (if u L then 1 else 0)

@[category API, AMS 11]
private lemma code_div_two (u : ℕ → Bool) (L : ℕ) : code u (L + 1) / 2 = code u L := by
  dsimp [code]
  rcases Bool.dichotomy (u L) with h | h
  · simp [h]
  · simp [h]; omega

@[category API, AMS 11]
private lemma code_mod_two (u : ℕ → Bool) (L : ℕ) :
    (if code u (L + 1) % 2 = 1 then (2 : ℝ) else 1) = (if u L then (2 : ℝ) else 1) := by
  dsimp [code]
  rcases Bool.dichotomy (u L) with h | h <;> simp [h]

@[category API, AMS 11]
private lemma code_lt_two_pow (u : ℕ → Bool) (L : ℕ) : code u L < 2 ^ L := by
  induction L with
  | zero => simp [code]
  | succ L ih =>
    dsimp [code]
    rw [Nat.pow_succ]
    rcases Bool.dichotomy (u L) with h | h <;> simp [h] <;> omega

/-- The block reserved for the first `L` bits of `u` has index at most `bound L`. -/
@[category API, AMS 11]
private lemma pair_code_le_bound (u : ℕ → Bool) (L : ℕ) : Nat.pair L (code u L) ≤ bound L := by
  have hL : L < 2 ^ L := Nat.lt_two_pow_self
  have hc : code u L < 2 ^ L := code_lt_two_pow u L
  have hsq : 2 ^ L * 2 ^ L = 4 ^ L := by rw [← mul_pow]; norm_num
  have hB : bound L = 4 * 4 ^ L := by dsimp [bound]; ring
  dsimp [Nat.pair]
  split_ifs <;> nlinarith

/-- The $i$-th term $(1 + u_i) 8^{-e(i)}$ of $\theta_u$. -/
private noncomputable def thetaTerm (u : ℕ → Bool) (i : ℕ) : ℝ :=
  (if u i then (2 : ℝ) else 1) * (1 / 8 : ℝ) ^ (expo i)

/-- The frequency $\theta_u$ attached to the bit sequence `u`. -/
private noncomputable def thetaSeq (u : ℕ → Bool) : ℝ := ∑' i, thetaTerm u i

/-- The truncation of $\theta_u$ after `L` terms, as a function of `L` and of the number
coded by the first `L` bits of `u`. -/
private noncomputable def thetaApprox : ℕ → ℕ → ℝ
  | 0, _ => 0
  | L + 1, m =>
    thetaApprox L (m / 2) + (if m % 2 = 1 then (2 : ℝ) else 1) * (1 / 8 : ℝ) ^ (expo L)

@[category API, AMS 11]
private lemma thetaApprox_code (u : ℕ → Bool) (L : ℕ) :
    thetaApprox L (code u L) = ∑ i ∈ Finset.range L, thetaTerm u i := by
  induction L with
  | zero => simp [thetaApprox]
  | succ L ih =>
    rw [Finset.sum_range_succ]
    dsimp [thetaApprox]
    rw [code_div_two, code_mod_two, ih]
    rfl

@[category API, AMS 11]
private lemma thetaTerm_bounds (u : ℕ → Bool) (i : ℕ) :
    (1 / 8 : ℝ) ^ (expo i) ≤ thetaTerm u i ∧ thetaTerm u i ≤ 2 * (1 / 8 : ℝ) ^ (expo i) := by
  dsimp [thetaTerm]
  have hpos : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ (expo i) := by positivity
  by_cases h : u i = true
  · rw [if_pos h]
    exact ⟨by linarith, by linarith⟩
  · rw [if_neg h]
    exact ⟨by linarith, by linarith⟩

@[category API, AMS 11]
private lemma thetaTerm_nonneg (u : ℕ → Bool) (i : ℕ) : 0 ≤ thetaTerm u i := by
  have := (thetaTerm_bounds u i).1
  have : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ (expo i) := by positivity
  linarith

@[category API, AMS 11]
private lemma thetaTerm_le_geom (u : ℕ → Bool) (i : ℕ) :
    thetaTerm u i ≤ (2 / 8 ^ 10 : ℝ) * (1 / 2 : ℝ) ^ i := by
  obtain ⟨_, ht⟩ := thetaTerm_bounds u i
  have hE : i + 10 ≤ expo i := by
    dsimp [expo, bound]
    have : 4 ≤ 4 ^ (i + 1) := by
      rw [Nat.pow_succ]
      have : 1 ≤ 4 ^ i := Nat.one_le_pow i 4 (by omega)
      omega
    omega
  have h1 : (1 / 8 : ℝ) ^ (expo i) ≤ (1 / 8 : ℝ) ^ (i + 10) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
  have h2 : (1 / 8 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ i := by gcongr; norm_num
  calc
    thetaTerm u i ≤ 2 * (1 / 8 : ℝ) ^ (expo i) := ht
    _ ≤ 2 * (1 / 8 : ℝ) ^ (i + 10) := by gcongr
    _ = (2 / 8 ^ 10 : ℝ) * (1 / 8 : ℝ) ^ i := by rw [pow_add]; ring
    _ ≤ (2 / 8 ^ 10 : ℝ) * (1 / 2 : ℝ) ^ i := by gcongr

@[category API, AMS 11]
private lemma summable_thetaTerm (u : ℕ → Bool) : Summable (thetaTerm u) := by
  have h_geom : Summable (fun i : ℕ => (2 / 8 ^ 10 : ℝ) * (1 / 2 : ℝ) ^ i) :=
    summable_geometric_two.mul_left _
  exact Summable.of_nonneg_of_le (thetaTerm_nonneg u) (thetaTerm_le_geom u) h_geom

@[category API, AMS 11]
private lemma thetaSeq_mem_Ioo (u : ℕ → Bool) : thetaSeq u ∈ Set.Ioo (0 : ℝ) 1 := by
  have h_sum := (summable_thetaTerm u).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h_sum
  have h_t0 : (1 / 8 : ℝ) ^ (expo 0) ≤ thetaTerm u 0 := (thetaTerm_bounds u 0).1
  have h_pos0 : (0 : ℝ) < (1 / 8 : ℝ) ^ (expo 0) := by positivity
  have h_tail_nonneg : 0 ≤ ∑' i, thetaTerm u (i + 1) :=
    tsum_nonneg (fun i => thetaTerm_nonneg u (i + 1))
  have h_gt0 : 0 < thetaSeq u := by
    dsimp [thetaSeq]
    linarith
  have h_le : thetaSeq u ≤ ∑' i : ℕ, (2 / 8 ^ 10 : ℝ) * (1 / 2 : ℝ) ^ i := by
    refine (summable_thetaTerm u).tsum_le_tsum (thetaTerm_le_geom u)
      (summable_geometric_two.mul_left _)
  have h_val : (∑' i : ℕ, (2 / 8 ^ 10 : ℝ) * (1 / 2 : ℝ) ^ i) = 4 / 8 ^ 10 := by
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  have h_lt1 : thetaSeq u < 1 := by linarith
  exact ⟨h_gt0, h_lt1⟩

@[category API, AMS 11]
private lemma thetaSeq_tail_succ_bound (u : ℕ → Bool) (k : ℕ) :
    ∑' j, thetaTerm u (j + (k + 1)) ≤ (1 / 2 : ℝ) * (1 / 8 : ℝ) ^ (expo k) := by
  have h_term : ∀ j, thetaTerm u (j + (k + 1)) ≤
      ((1 / 4 : ℝ) * (1 / 8 : ℝ) ^ (expo k)) * (1 / 2 : ℝ) ^ j := fun j => by
    have hj : j + (k + 1) = j + k + 1 := by omega
    rw [hj]
    obtain ⟨_, ht⟩ := thetaTerm_bounds u (j + k + 1)
    have hE := expo_add_succ_le k j
    have h1 : (1 / 8 : ℝ) ^ (expo (j + k + 1)) ≤ (1 / 8 : ℝ) ^ (expo k + j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
    have h2 : (1 / 8 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j := by gcongr; norm_num
    calc
      thetaTerm u (j + k + 1) ≤ 2 * (1 / 8 : ℝ) ^ (expo (j + k + 1)) := ht
      _ ≤ 2 * (1 / 8 : ℝ) ^ (expo k + j + 1) := by gcongr
      _ = ((1 / 4 : ℝ) * (1 / 8 : ℝ) ^ (expo k)) * (1 / 8 : ℝ) ^ j := by
        rw [pow_add, pow_add]
        ring
      _ ≤ ((1 / 4 : ℝ) * (1 / 8 : ℝ) ^ (expo k)) * (1 / 2 : ℝ) ^ j := by gcongr
  have h_sum_lhs : Summable (fun j => thetaTerm u (j + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).mpr (summable_thetaTerm u)
  have h_sum_rhs :
      Summable (fun j : ℕ => ((1 / 4 : ℝ) * (1 / 8 : ℝ) ^ (expo k)) * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  have h_le := h_sum_lhs.tsum_le_tsum h_term h_sum_rhs
  have h_rhs : (∑' j : ℕ, ((1 / 4 : ℝ) * (1 / 8 : ℝ) ^ (expo k)) * (1 / 2 : ℝ) ^ j) =
      (1 / 2 : ℝ) * (1 / 8 : ℝ) ^ (expo k) := by
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  linarith

/-- Distinct bit sequences give distinct frequencies. -/
@[category API, AMS 11]
private lemma thetaSeq_injective : Function.Injective thetaSeq := by
  intro u v huv
  by_contra hne
  have hex : ∃ k, u k ≠ v k := Function.ne_iff.mp hne
  classical
  let k := Nat.find hex
  have hk_ne : u k ≠ v k := Nat.find_spec hex
  have hk_lt : ∀ j < k, u j = v j := fun j hj => by
    by_contra h_ne
    exact Nat.find_min hex hj h_ne
  have h_pref : ∑ j ∈ Finset.range k, thetaTerm u j = ∑ j ∈ Finset.range k, thetaTerm v j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    dsimp [thetaTerm]
    rw [hk_lt j hj]
  have h_split_u := (summable_thetaTerm u).sum_add_tsum_nat_add (k + 1)
  have h_split_v := (summable_thetaTerm v).sum_add_tsum_nat_add (k + 1)
  rw [Finset.sum_range_succ] at h_split_u h_split_v
  have h_tu_0 : 0 ≤ ∑' j, thetaTerm u (j + (k + 1)) :=
    tsum_nonneg (fun j => thetaTerm_nonneg u (j + (k + 1)))
  have h_tv_0 : 0 ≤ ∑' j, thetaTerm v (j + (k + 1)) :=
    tsum_nonneg (fun j => thetaTerm_nonneg v (j + (k + 1)))
  have h_tu_1 := thetaSeq_tail_succ_bound u k
  have h_tv_1 := thetaSeq_tail_succ_bound v k
  have h_pos : (0 : ℝ) < (1 / 8 : ℝ) ^ (expo k) := by positivity
  have h_diff : (thetaTerm u k - thetaTerm v k) +
      (∑' j, thetaTerm u (j + (k + 1))) - (∑' j, thetaTerm v (j + (k + 1))) = 0 := by
    dsimp [thetaSeq] at huv
    linarith
  cases h_uk : u k <;> cases h_vk : v k
  · exact hk_ne (h_uk.trans h_vk.symm)
  · have h_tk : thetaTerm u k - thetaTerm v k = - (1 / 8 : ℝ) ^ (expo k) := by
      dsimp [thetaTerm]
      rw [h_uk, h_vk]
      simp
      ring
    linarith
  · have h_tk : thetaTerm u k - thetaTerm v k = (1 / 8 : ℝ) ^ (expo k) := by
      dsimp [thetaTerm]
      rw [h_uk, h_vk]
      simp
      ring
    linarith
  · exact hk_ne (h_uk.trans h_vk.symm)

/-- On the block reserved for the first `L` bits of `u`, replacing $\theta_u$ by its
truncation after `L` terms changes $n \theta_u$ by at most $1/512$. -/
@[category API, AMS 11]
private lemma thetaSeq_tail_mul_bound (u : ℕ → Bool) (L k m : ℕ)
    (hk : k ≤ bound L) (hm : m ≤ 6 * scale k) :
    0 ≤ (m : ℝ) * (thetaSeq u - ∑ i ∈ Finset.range L, thetaTerm u i) ∧
      (m : ℝ) * (thetaSeq u - ∑ i ∈ Finset.range L, thetaTerm u i) ≤ 1 / 512 := by
  have h_sum := (summable_thetaTerm u).sum_add_tsum_nat_add L
  have h_diff : thetaSeq u - ∑ i ∈ Finset.range L, thetaTerm u i = ∑' j, thetaTerm u (j + L) := by
    dsimp [thetaSeq]
    linarith
  rw [h_diff, ← tsum_mul_left]
  have h_nonneg : ∀ j, 0 ≤ (m : ℝ) * thetaTerm u (j + L) := fun j =>
    mul_nonneg (by positivity) (thetaTerm_nonneg u (j + L))
  refine ⟨tsum_nonneg h_nonneg, ?_⟩
  have hm_le : m ≤ 120 * 8 ^ (bound L) := by
    have hM : scale k ≤ scale (bound L) := scale_mono hk
    dsimp [scale] at hM hm
    omega
  have hm_real : (m : ℝ) ≤ 120 * (8 : ℝ) ^ (bound L) := by exact_mod_cast hm_le
  have h_term : ∀ j, (m : ℝ) * thetaTerm u (j + L) ≤ (1 / 1024 : ℝ) * (1 / 2 : ℝ) ^ j := fun j => by
    obtain ⟨_, ht⟩ := thetaTerm_bounds u (j + L)
    have hE := le_expo_add L j
    have h1 : (1 / 8 : ℝ) ^ (expo (j + L)) ≤ (1 / 8 : ℝ) ^ (bound L + j + 6) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
    have h_cancel : (8 : ℝ) ^ (bound L) * (1 / 8 : ℝ) ^ (bound L) = 1 := by
      rw [← mul_pow]
      norm_num
    have h2 : (1 / 8 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j := by gcongr; norm_num
    calc
      (m : ℝ) * thetaTerm u (j + L)
        ≤ (120 * (8 : ℝ) ^ (bound L)) * (2 * (1 / 8 : ℝ) ^ (expo (j + L))) := by
          gcongr
          exact thetaTerm_nonneg u (j + L)
      _ ≤ (120 * (8 : ℝ) ^ (bound L)) * (2 * (1 / 8 : ℝ) ^ (bound L + j + 6)) := by gcongr
      _ = 240 * ((8 : ℝ) ^ (bound L) * (1 / 8 : ℝ) ^ (bound L)) * (1 / 8 : ℝ) ^ 6 *
            (1 / 8 : ℝ) ^ j := by
        rw [pow_add, pow_add]
        ring
      _ = (15 / 16384 : ℝ) * (1 / 8 : ℝ) ^ j := by rw [h_cancel]; ring
      _ ≤ (1 / 1024 : ℝ) * (1 / 2 : ℝ) ^ j := by
        calc
          (15 / 16384 : ℝ) * (1 / 8 : ℝ) ^ j ≤ (15 / 16384 : ℝ) * (1 / 2 : ℝ) ^ j := by gcongr
          _ ≤ (1 / 1024 : ℝ) * (1 / 2 : ℝ) ^ j :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have h_sum_lhs : Summable (fun j => (m : ℝ) * thetaTerm u (j + L)) :=
    ((summable_nat_add_iff L).mpr (summable_thetaTerm u)).mul_left _
  have h_sum_rhs : Summable (fun j : ℕ => (1 / 1024 : ℝ) * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  have h_le := h_sum_lhs.tsum_le_tsum h_term h_sum_rhs
  have h_rhs : (∑' j : ℕ, (1 / 1024 : ℝ) * (1 / 2 : ℝ) ^ j) = 1 / 512 := by
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  linarith

/-! ### The real number $\xi$ -/

/-- The value that $\xi 64^n$ has to shadow modulo one at the index `n`. -/
private noncomputable def targetSeq (n : ℕ) : ℝ :=
  (n : ℝ) * thetaApprox (Nat.unpair (blockIdx n)).1 (Nat.unpair (blockIdx n)).2

/-- The `n`-th base-$64$ digit of $\xi$, shifted by `2` to keep it away from the endpoints. -/
private noncomputable def digit (n : ℕ) : ℤ :=
  ⌊64 * Int.fract (targetSeq n)⌋ + 2

private noncomputable def xiTerm (j : ℕ) : ℝ :=
  (digit j : ℝ) * (1 / 64 : ℝ) ^ (j + 1)

/-- The counterexample $\xi = \sum_j d_j 64^{-(j+1)}$. -/
private noncomputable def xiVal : ℝ := ∑' j, xiTerm j

@[category API, AMS 11]
private lemma digit_bounds (n : ℕ) :
    1 ≤ (digit n : ℝ) ∧ (digit n : ℝ) ≤ 66 ∧
      1 / 64 < (digit n : ℝ) / 64 - Int.fract (targetSeq n) ∧
      (digit n : ℝ) / 64 - Int.fract (targetSeq n) ≤ 2 / 64 := by
  have hf0 : 0 ≤ Int.fract (targetSeq n) := Int.fract_nonneg _
  have hf1 : Int.fract (targetSeq n) < 1 := Int.fract_lt_one _
  have hfl1 : (⌊64 * Int.fract (targetSeq n)⌋ : ℝ) ≤ 64 * Int.fract (targetSeq n) := Int.floor_le _
  have hfl2 : 64 * Int.fract (targetSeq n) < (⌊64 * Int.fract (targetSeq n)⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hd : (digit n : ℝ) = (⌊64 * Int.fract (targetSeq n)⌋ : ℝ) + 2 := by
    dsimp [digit]
    push_cast
    ring
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

@[category API, AMS 11]
private lemma xiTerm_nonneg (j : ℕ) : 0 ≤ xiTerm j := by
  dsimp [xiTerm]
  have hd := (digit_bounds j).1
  have : (0 : ℝ) ≤ (1 / 64 : ℝ) ^ (j + 1) := by positivity
  exact mul_nonneg (by linarith) this

@[category API, AMS 11]
private lemma xiTerm_mul_pow_bound (n j : ℕ) :
    xiTerm (j + (n + 1)) * (64 : ℝ) ^ n ≤ (33 / 2048 : ℝ) * (1 / 2 : ℝ) ^ j := by
  dsimp [xiTerm]
  have hd := (digit_bounds (j + (n + 1))).2.1
  have hexp : j + (n + 1) + 1 = (j + 2) + n := by omega
  rw [hexp, pow_add, mul_assoc]
  have h_cancel : (1 / 64 : ℝ) ^ n * (64 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [mul_assoc, h_cancel, mul_one]
  have h2 : (1 / 64 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j := by gcongr; norm_num
  calc
    (digit (j + (n + 1)) : ℝ) * (1 / 64 : ℝ) ^ (j + 2)
      ≤ 66 * (1 / 64 : ℝ) ^ (j + 2) := by gcongr
    _ = (33 / 2048 : ℝ) * (1 / 64 : ℝ) ^ j := by rw [pow_add]; ring
    _ ≤ (33 / 2048 : ℝ) * (1 / 2 : ℝ) ^ j := by gcongr

@[category API, AMS 11]
private lemma summable_xiTerm : Summable xiTerm := by
  have h_geom : Summable (fun j : ℕ => (33 / 2048 : ℝ) * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun j => xiTerm_nonneg (j + 1)) (fun j => ?_) h_geom
  have h := xiTerm_mul_pow_bound 0 j
  simpa using h

@[category API, AMS 11]
private lemma xiVal_ne_zero : xiVal ≠ 0 := by
  have h_sum := summable_xiTerm.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h_sum
  have hd0 := (digit_bounds 0).1
  have ht0 : 1 / 64 ≤ xiTerm 0 := by
    dsimp [xiTerm]
    linarith
  have h_tail : 0 ≤ ∑' j, xiTerm (j + 1) := tsum_nonneg (fun j => xiTerm_nonneg (j + 1))
  dsimp [xiVal]
  linarith

@[category API, AMS 11]
private lemma xiVal_tail_bounds (n : ℕ) :
    0 ≤ (xiVal - ∑ j ∈ Finset.range (n + 1), xiTerm j) * (64 : ℝ) ^ n ∧
      (xiVal - ∑ j ∈ Finset.range (n + 1), xiTerm j) * (64 : ℝ) ^ n ≤ 33 / 1024 := by
  have h_sum := summable_xiTerm.sum_add_tsum_nat_add (n + 1)
  have h_diff : xiVal - ∑ j ∈ Finset.range (n + 1), xiTerm j = ∑' j, xiTerm (j + (n + 1)) := by
    dsimp [xiVal]
    linarith
  rw [h_diff, ← tsum_mul_right]
  have h_nonneg : ∀ j, 0 ≤ xiTerm (j + (n + 1)) * (64 : ℝ) ^ n := fun j =>
    mul_nonneg (xiTerm_nonneg _) (by positivity)
  refine ⟨tsum_nonneg h_nonneg, ?_⟩
  have h_sum_lhs : Summable (fun j => xiTerm (j + (n + 1)) * (64 : ℝ) ^ n) :=
    ((summable_nat_add_iff (n + 1)).mpr summable_xiTerm).mul_right _
  have h_sum_rhs : Summable (fun j : ℕ => (33 / 2048 : ℝ) * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  have h_le := h_sum_lhs.tsum_le_tsum (xiTerm_mul_pow_bound n) h_sum_rhs
  have h_rhs : (∑' j : ℕ, (33 / 2048 : ℝ) * (1 / 2 : ℝ) ^ j) = 33 / 1024 := by
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  linarith

/-- The integer $\sum_{j < n} d_j 64^{n - 1 - j}$ formed by the digits of $\xi$ before `n`. -/
private noncomputable def prefixInt (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range n, digit j * (64 : ℤ) ^ (n - 1 - j)

@[category API, AMS 11]
private lemma sum_xiTerm_mul_pow (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), xiTerm j) * (64 : ℝ) ^ n =
      (prefixInt n : ℝ) + (digit n : ℝ) / 64 := by
  rw [Finset.sum_range_succ, add_mul, Finset.sum_mul]
  have h_last : xiTerm n * (64 : ℝ) ^ n = (digit n : ℝ) / 64 := by
    have h_one : (1 / 64 : ℝ) ^ n * (64 : ℝ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    calc
      xiTerm n * (64 : ℝ) ^ n
        = (digit n : ℝ) * (1 / 64 : ℝ) * ((1 / 64 : ℝ) ^ n * (64 : ℝ) ^ n) := by
          dsimp [xiTerm]; rw [pow_succ]; ring
      _ = (digit n : ℝ) / 64 := by rw [h_one]; ring
  have h_pref : ∑ j ∈ Finset.range n, xiTerm j * (64 : ℝ) ^ n = (prefixInt n : ℝ) := by
    dsimp [prefixInt]
    push_cast
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    dsimp [xiTerm]
    have h_split : n = (n - 1 - j) + (j + 1) := by omega
    conv_lhs => rw [h_split, pow_add (64 : ℝ)]
    have h_one : (1 / 64 : ℝ) ^ (j + 1) * (64 : ℝ) ^ (j + 1) = 1 := by
      rw [← mul_pow]; norm_num
    calc
      (digit j : ℝ) * (1 / 64 : ℝ) ^ (j + 1) * ((64 : ℝ) ^ (n - 1 - j) * (64 : ℝ) ^ (j + 1))
        = (digit j : ℝ) * (64 : ℝ) ^ (n - 1 - j) *
            ((1 / 64 : ℝ) ^ (j + 1) * (64 : ℝ) ^ (j + 1)) := by ring
      _ = (digit j : ℝ) * (64 : ℝ) ^ (n - 1 - j) := by rw [h_one, mul_one]
  rw [h_pref, h_last]

/-! ### Failure of uniform distribution -/

/-- On the block reserved for the first `L` bits of `u`, the fractional part of
$\xi 64^m - m \theta_u$ is smaller than $1/10$. -/
@[category API, AMS 11]
private lemma fract_notMem_Icc (u : ℕ → Bool) (L m : ℕ)
    (hm1 : 5 * scale (Nat.pair L (code u L)) ≤ m)
    (hm2 : m < 6 * scale (Nat.pair L (code u L))) :
    Int.fract (xiVal * (64 : ℝ) ^ m - (m : ℝ) * thetaSeq u) ∉ Set.Icc (1 / 10 : ℝ) 1 := by
  set k := Nat.pair L (code u L)
  have h_blk : blockIdx m = k := blockIdx_eq_of_mem hm1 hm2
  have h_target : targetSeq m = (m : ℝ) * ∑ i ∈ Finset.range L, thetaTerm u i := by
    dsimp [targetSeq]
    rw [h_blk, Nat.unpair_pair, thetaApprox_code]
  have hk_le : k ≤ bound L := pair_code_le_bound u L
  obtain ⟨htheta0, htheta1⟩ := thetaSeq_tail_mul_bound u L k m hk_le (by omega)
  rw [mul_sub, ← h_target] at htheta0 htheta1
  obtain ⟨hxi0, hxi1⟩ := xiVal_tail_bounds m
  obtain ⟨_, _, hd1, hd2⟩ := digit_bounds m
  let N_int : ℤ := prefixInt m - ⌊targetSeq m⌋
  set tail_xi := (xiVal - ∑ j ∈ Finset.range (m + 1), xiTerm j) * (64 : ℝ) ^ m
  set tail_th := (m : ℝ) * thetaSeq u - targetSeq m
  set δ := ((digit m : ℝ) / 64 - Int.fract (targetSeq m)) + tail_xi - tail_th
  have hy_split : targetSeq m = (⌊targetSeq m⌋ : ℝ) + Int.fract (targetSeq m) :=
    (Int.floor_add_fract (targetSeq m)).symm
  have hxi_split : xiVal * (64 : ℝ) ^ m =
      (prefixInt m : ℝ) + (digit m : ℝ) / 64 + tail_xi := by
    dsimp [tail_xi]
    have h_pref := sum_xiTerm_mul_pow m
    linarith
  have h_eq : xiVal * (64 : ℝ) ^ m - (m : ℝ) * thetaSeq u = (N_int : ℝ) + δ := by
    dsimp [N_int, δ, tail_th]
    push_cast
    linarith
  have hδ0 : 0 ≤ δ := by dsimp [δ]; linarith
  have hδ_tenth : δ < 1 / 10 := by dsimp [δ]; linarith
  have h_fract : Int.fract (xiVal * (64 : ℝ) ^ m - (m : ℝ) * thetaSeq u) = δ := by
    rw [h_eq, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hδ0, by linarith⟩]
  rw [h_fract]
  intro h_mem
  exact absurd h_mem.1 (by linarith)

/-- For every bit sequence `u`, the sequence $(\xi 64^n - n \theta_u)$ is not uniformly
distributed modulo one. -/
@[category API, AMS 11]
private lemma not_isEquidistributedModuloOne (u : ℕ → Bool) :
    ¬ IsEquidistributedModuloOne (fun n ↦ xiVal * (64 : ℝ) ^ n - (n : ℝ) * thetaSeq u) := by
  intro h_eq
  have h_sub : Set.Icc (1 / 10 : ℝ) 1 ⊆ Set.Icc 0 1 :=
    Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have h_tendsto := h_eq (1 / 10) 1 (by norm_num) h_sub
  have h_lim : ((1 : ℝ) - 1 / 10) / (1 - 0) = 9 / 10 := by ring
  rw [h_lim] at h_tendsto
  have h_ev := h_tendsto.eventually (Ioi_mem_nhds (by norm_num : (89 / 100 : ℝ) < 9 / 10))
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨L, hL⟩ := h_ev
  set k := Nat.pair L (code u L)
  set n := 6 * scale k - 6
  have hLk : L ≤ k := Nat.left_le_pair L (code u L)
  have hMk20 : 20 ≤ scale k := twenty_le_scale k
  have hMk_k : k + 20 ≤ scale k := add_twenty_le_scale k
  have hn_ge : L ≤ n := by omega
  have h_gt : (89 / 100 : ℝ) <
      ((Finset.range n).filter
        (fun m : ℕ => Int.fract (xiVal * (64 : ℝ) ^ m - (m : ℝ) * thetaSeq u) ∈
          Set.Icc (1 / 10) 1)).card / (n : ℝ) :=
    hL n hn_ge
  let A := (Finset.range n).filter
    (fun m : ℕ => Int.fract (xiVal * (64 : ℝ) ^ m - (m : ℝ) * thetaSeq u) ∈ Set.Icc (1 / 10) 1)
  let blockSet := Finset.Ico (5 * scale k) n
  have h_sub_range : A ∪ blockSet ⊆ Finset.range n := by
    refine Finset.union_subset (Finset.filter_subset _ _) ?_
    intro m hm
    rw [Finset.mem_Ico] at hm
    exact Finset.mem_range.mpr hm.2
  have h_disj : Disjoint A blockSet := by
    rw [Finset.disjoint_left]
    intro m hmA hmB
    rw [Finset.mem_filter] at hmA
    rw [Finset.mem_Ico] at hmB
    have hm_lt : m < 6 * scale k := by
      have : m < 6 * scale k - 6 := hmB.2
      omega
    exact fract_notMem_Icc u L m hmB.1 hm_lt hmA.2
  have h_card_union : A.card + blockSet.card ≤ n := by
    calc
      A.card + blockSet.card = (A ∪ blockSet).card := (Finset.card_union_of_disjoint h_disj).symm
      _ ≤ (Finset.range n).card := Finset.card_le_card h_sub_range
      _ = n := Finset.card_range n
  have h_block_card : blockSet.card = scale k - 6 := by
    dsimp [blockSet, n]
    rw [Nat.card_Ico]
    omega
  have h_A_le : A.card ≤ 5 * scale k := by omega
  have h_A_real : (A.card : ℝ) ≤ 5 * (scale k : ℝ) := by exact_mod_cast h_A_le
  have hn_real : (n : ℝ) = 6 * (scale k : ℝ) - 6 := by
    have h6 : 6 ≤ 6 * scale k := by omega
    change ((6 * scale k - 6 : ℕ) : ℝ) = 6 * (scale k : ℝ) - 6
    rw [Nat.cast_sub h6]
    push_cast
    ring
  have hMk_real : (20 : ℝ) ≤ (scale k : ℝ) := by exact_mod_cast hMk20
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    rw [hn_real]
    linarith
  have h_num_le : (A.card : ℝ) ≤ 89 / 100 * (n : ℝ) := by
    calc
      (A.card : ℝ) ≤ 5 * (scale k : ℝ) := h_A_real
      _ ≤ 89 / 100 * (6 * (scale k : ℝ) - 6) := by linarith
      _ = 89 / 100 * (n : ℝ) := by rw [hn_real]
  have h_div_le : (A.card : ℝ) / (n : ℝ) ≤ 89 / 100 := by
    rw [div_le_iff₀ hn_pos]
    exact h_num_le
  exact absurd h_gt (not_lt_of_ge h_div_le)

/--
Problem 10.4. Let $\xi$ be a non-zero real number and $\alpha > 1$ be a real
number. Is the spectrum of the sequence $(\xi \alpha^n)_{n \ge 1}$ at most
countable? Posed by Mendès France [Men73].

The answer is no. Özcan [Özc26] disproved this for every $\alpha > 1$; the counterexample
formalised here takes $\alpha = 64$ and the real number $\xi = $ `xiVal`, whose spectrum
contains the uncountable set of irrational numbers of the form `thetaSeq u`.
-/
@[category research solved, AMS 11]
theorem spectrum_xi_alpha_pow_countable : answer(False) ↔
    ∀ (ξ : ℝ), ξ ≠ 0 → ∀ (α : ℝ), 1 < α → (Spectrum (fun n => ξ * α ^ n)).Countable := by
  constructor
  · intro h
    exact h.elim
  · intro h
    have h_spec : (Spectrum (fun n => xiVal * (64 : ℝ) ^ n)).Countable :=
      h xiVal xiVal_ne_zero 64 (by norm_num)
    -- Every `thetaSeq u` is either rational or in the spectrum, so this set is countable.
    let Bad : Set ℝ := Set.range (algebraMap ℚ ℝ) ∪ Spectrum (fun n => xiVal * (64 : ℝ) ^ n)
    have h_bad_cnt : Bad.Countable := (Set.countable_range (algebraMap ℚ ℝ)).union h_spec
    have h_coe_cnt : Countable Bad := Set.countable_coe_iff.mpr h_bad_cnt
    have h_mem : ∀ u : ℕ → Bool, thetaSeq u ∈ Bad := fun u => by
      by_cases hirr : Irrational (thetaSeq u)
      · exact Or.inr ⟨thetaSeq_mem_Ioo u, hirr, not_isEquidistributedModuloOne u⟩
      · unfold Irrational at hirr
        push Not at hirr
        exact Or.inl hirr
    -- But `u ↦ thetaSeq u` is injective on the uncountable set of bit sequences.
    let F : (ℕ → Bool) → Bad := fun u => ⟨thetaSeq u, h_mem u⟩
    have hF : Function.Injective F := fun u v huv => thetaSeq_injective (congr_arg Subtype.val huv)
    have : Countable (ℕ → Bool) := hF.countable
    -- Cantor's diagonal argument contradicts the countability of `ℕ → Bool`.
    obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
    obtain ⟨n, hn⟩ := hg (fun k => !(g k k))
    have hnn : g n n = !(g n n) := congr_fun hn n
    revert hnn
    cases g n n <;> decide

end Bugeaud04
