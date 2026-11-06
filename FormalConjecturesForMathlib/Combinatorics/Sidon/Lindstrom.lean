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
module

public import FormalConjecturesForMathlib.Combinatorics.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Lindström's upper bound for Sidon sets

For a Sidon set $A \subseteq \{1, \dots, N\}$ with $k = |A|$ and a window length
$1 \le m \le k - 1$, the $M = \sum_{\ell=1}^{m} (k - \ell)$ differences $a_{i+\ell} - a_i$ are
pairwise distinct positive integers (so their sum is at least $M(M+1)/2$) and, by telescoping,
their sum is at most $(N-1) m (m+1) / 2$. Choosing $m = \lceil N^{1/4} \rceil$ gives Lindström's
bound $k \le \sqrt N + N^{1/4} + 1$.

*References:*
- [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on
  some related problems*. J. London Math. Soc. 16 (1941), 212-215.
- [Li69] Lindström, B., *An inequality for $B_2$-sequences*. J. Combinatorial Theory 6 (1969),
  211-212.
-/

@[expose] public section

open Finset

namespace Finset

/-- A finite set of `t` positive natural numbers has sum at least `t * (t + 1) / 2`. -/
theorem card_mul_succ_le_two_mul_sum_of_pos (t : Finset ℕ) (ht : ∀ x ∈ t, 0 < x) :
    #t * (#t + 1) ≤ 2 * ∑ x ∈ t, x := by
  induction t using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl _ (hlt a h)
    have hs : ∀ x ∈ s, 0 < x := fun x hx ↦ ht x (mem_insert_of_mem hx)
    have hsub : s ⊆ Ico 1 a := fun x hx ↦ mem_Ico.2 ⟨hs x hx, hlt x hx⟩
    have hcard : #s + 1 ≤ a := by
      have := card_le_card hsub
      rw [Nat.card_Ico] at this
      have := ht a (mem_insert_self _ _)
      omega
    rw [card_insert_of_notMem has, sum_insert has]
    nlinarith [ih hs]

/-- A finite family of pairwise distinct positive natural numbers indexed by `s` has sum at least
`#s * (#s + 1) / 2`. -/
theorem card_mul_succ_le_two_mul_sum_of_injOn {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) (hpos : ∀ i ∈ s, 0 < f i) :
    #s * (#s + 1) ≤ 2 * ∑ i ∈ s, f i := by
  have h := card_mul_succ_le_two_mul_sum_of_pos (s.image f) (by simpa using hpos)
  rwa [card_image_of_injOn hf, sum_image hf] at h

/-- Gauss's formula for `∑ ℓ ∈ Icc 1 m, ℓ`, in the form `2 * ∑ = m * (m + 1)`. -/
theorem two_mul_sum_Icc_id (m : ℕ) : 2 * ∑ ℓ ∈ Icc 1 m, ℓ = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_Icc_succ_top (by omega), mul_add, ih]; ring

/-- Pure arithmetic: the number of windows of lengths `1, …, m` in a list of length `k`. -/
theorem two_mul_sum_Icc_sub {k m : ℕ} (hmk : m + 1 ≤ k) :
    2 * ∑ ℓ ∈ Icc 1 m, (k - ℓ) = 2 * m * k - m * (m + 1) := by
  have key : ∀ m, m + 1 ≤ k → 2 * ∑ ℓ ∈ Icc 1 m, (k - ℓ) + m * (m + 1) = 2 * m * k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro h
      have := ih (by omega)
      obtain ⟨c, rfl⟩ : ∃ c, k = c + m + 1 := ⟨k - (m + 1), by omega⟩
      rw [sum_Icc_succ_top (by omega), show c + m + 1 - (m + 1) = c by omega]
      nlinarith
  have := key m hmk
  omega

/-- Telescoping bound for one window length `ℓ`: for a strictly increasing enumeration `a` of
`k` values in `[1, N]`, `∑ i < k - ℓ, (a (i + ℓ) - a i) ≤ ℓ * (N - 1)`. -/
theorem sum_window_diff_le {a : ℕ → ℕ} {N k : ℕ} (hmono : ∀ i j, i < j → j < k → a i < a j)
    (hlo : ∀ i < k, 1 ≤ a i) (hhi : ∀ i < k, a i ≤ N) {ℓ : ℕ} (hℓ : ℓ ≤ k) :
    ∑ i ∈ range (k - ℓ), (a (i + ℓ) - a i) ≤ ℓ * (N - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + ℓ := ⟨k - ℓ, by omega⟩
  rw [Nat.add_sub_cancel]
  have h1 : ∑ i ∈ range n, (a (i + ℓ) - a i) + ∑ i ∈ range n, a i = ∑ i ∈ range n, a (i + ℓ) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi := mem_range.1 hi
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
    · simp
    · have := hmono i (i + ℓ) (by omega) (by omega)
      omega
  have h2 := sum_range_add a ℓ n
  have h3 := sum_range_add a n ℓ
  have h4 : ∑ x ∈ range ℓ, a (n + x) ≤ ℓ * N := by
    simpa using sum_le_card_nsmul (range ℓ) (fun x ↦ a (n + x)) N
      fun x hx ↦ hhi _ (by have := mem_range.1 hx; omega)
  have h5 : ℓ ≤ ∑ x ∈ range ℓ, a x := by
    simpa using card_nsmul_le_sum (range ℓ) a 1 fun x hx ↦ hlo _ (by have := mem_range.1 hx; omega)
  have h6 : ∑ x ∈ range n, a (ℓ + x) = ∑ x ∈ range n, a (x + ℓ) :=
    sum_congr rfl fun x _ ↦ by rw [add_comm]
  have h7 : ℓ * (N - 1) + ℓ = ℓ * N := by
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
    · simp
    · have := hlo 0 (by omega)
      have := hhi 0 (by omega)
      rw [← Nat.mul_succ]; congr 1; omega
  rw [add_comm ℓ n] at h2
  omega

/-- In a Sidon set, a positive difference determines its endpoints: if `a₁ - b₁ = a₂ - b₂` with
`b₁ < a₁` and `b₂ < a₂`, then `a₁ = a₂` and `b₁ = b₂`. -/
theorem IsSidon.eq_of_sub_eq {A : Finset ℕ} (hS : IsSidon (A : Set ℕ))
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (hlt₁ : b₁ < a₁) (hlt₂ : b₂ < a₂) (heq : a₁ - b₁ = a₂ - b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  rcases hS a₁ ha₁ a₂ ha₂ b₂ hb₂ b₁ hb₁ (by omega) with h | h <;> omega

/-- The counting step, in terms of an explicit enumeration `a` of `k` elements of the Sidon set. -/
theorem IsSidon.lindstrom_count_of_enum {A : Finset ℕ} (hS : IsSidon (A : Set ℕ)) {N k : ℕ}
    {a : ℕ → ℕ} (hmem : ∀ i < k, a i ∈ A) (hmono : ∀ i j, i < j → j < k → a i < a j)
    (hlo : ∀ i < k, 1 ≤ a i) (hhi : ∀ i < k, a i ≤ N) {m : ℕ} (hmk : m + 1 ≤ k) :
    (∑ ℓ ∈ Icc 1 m, (k - ℓ)) * ((∑ ℓ ∈ Icc 1 m, (k - ℓ)) + 1) ≤ m * (m + 1) * (N - 1) := by
  have hinj : ∀ i j, i < k → j < k → a i = a j → i = j := fun i j hi hj h ↦ by
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (hmono i j h' hj).ne
    · exact h'
    · exact absurd h (hmono j i h' hi).ne'
  let T : Finset (Σ _ : ℕ, ℕ) := (Icc 1 m).sigma fun ℓ ↦ range (k - ℓ)
  let d : (Σ _ : ℕ, ℕ) → ℕ := fun p ↦ a (p.2 + p.1) - a p.2
  have hT : ∀ p ∈ T, 1 ≤ p.1 ∧ p.1 ≤ m ∧ p.2 + p.1 < k := fun ⟨ℓ, i⟩ hp ↦ by
    simp only [T, mem_sigma, mem_Icc, mem_range] at hp ⊢
    omega
  have hcard : #T = ∑ ℓ ∈ Icc 1 m, (k - ℓ) := by simp [T, card_sigma]
  have hdinj : Set.InjOn d T := by
    rintro ⟨ℓ, i⟩ hp ⟨ℓ', i'⟩ hq heq
    obtain ⟨h1, h2, h3⟩ := hT _ hp
    obtain ⟨h1', h2', h3'⟩ := hT _ hq
    simp only at h1 h2 h3 h1' h2' h3'
    have hlt : a i < a (i + ℓ) := hmono _ _ (by omega) h3
    have hlt' : a i' < a (i' + ℓ') := hmono _ _ (by omega) h3'
    obtain ⟨e1, e2⟩ := IsSidon.eq_of_sub_eq hS (hmem _ h3) (hmem _ (by omega)) (hmem _ h3')
      (hmem _ (by omega)) hlt hlt' heq
    have := hinj _ _ h3 h3' e1
    have := hinj _ _ (by omega) (by omega) e2
    obtain rfl : i = i' := by omega
    obtain rfl : ℓ = ℓ' := by omega
    rfl
  have hdpos : ∀ p ∈ T, 0 < d p := fun p hp ↦ by
    obtain ⟨h1, h2, h3⟩ := hT p hp
    have := hmono p.2 (p.2 + p.1) (by omega) h3
    simp only [d]; omega
  have hlow := card_mul_succ_le_two_mul_sum_of_injOn T d hdinj hdpos
  have hup : ∑ p ∈ T, d p ≤ ∑ ℓ ∈ Icc 1 m, ℓ * (N - 1) := by
    rw [sum_sigma]
    refine sum_le_sum fun ℓ hℓ ↦ ?_
    obtain ⟨h1, h2⟩ := mem_Icc.1 hℓ
    exact sum_window_diff_le hmono hlo hhi (by omega)
  rw [← sum_mul] at hup
  have hg := two_mul_sum_Icc_id m
  rw [hcard] at hlow
  calc _ ≤ 2 * ∑ p ∈ T, d p := hlow
    _ ≤ 2 * ((∑ ℓ ∈ Icc 1 m, ℓ) * (N - 1)) := by omega
    _ = m * (m + 1) * (N - 1) := by rw [← mul_assoc, hg]

/-- L1 (counting step, natural numbers). -/
theorem IsSidon.lindstrom_count {A : Finset ℕ} (hS : IsSidon (A : Set ℕ)) {N : ℕ}
    (hA : A ⊆ Icc 1 N) {m : ℕ} (_hm : 1 ≤ m) (hmk : m + 1 ≤ #A) :
    (∑ ℓ ∈ Icc 1 m, (#A - ℓ)) * ((∑ ℓ ∈ Icc 1 m, (#A - ℓ)) + 1) ≤ m * (m + 1) * (N - 1) := by
  let f := A.orderEmbOfFin rfl
  let a : ℕ → ℕ := fun i ↦ if h : i < #A then f ⟨i, h⟩ else 0
  have hmem : ∀ i < #A, a i ∈ A := fun i hi ↦ by
    rw [show a i = f ⟨i, hi⟩ from dif_pos hi]
    exact A.orderEmbOfFin_mem rfl ⟨i, hi⟩
  refine hS.lindstrom_count_of_enum hmem (fun i j hij hj ↦ ?_) (fun i hi ↦ ?_) (fun i hi ↦ ?_) hmk
  · have hi : i < #A := hij.trans hj
    rw [show a i = f ⟨i, hi⟩ from dif_pos hi, show a j = f ⟨j, hj⟩ from dif_pos hj]
    exact f.strictMono (Fin.mk_lt_mk.2 hij)
  · exact (mem_Icc.1 (hA (hmem i hi))).1
  · exact (mem_Icc.1 (hA (hmem i hi))).2

end Finset


/-- Real form of the counting inequality: `(k - (m + 1) / 2) ^ 2 * m ≤ (m + 1) * N`. -/
lemma Finset.lindstrom_sq_bound {k m N : ℕ} (hm : 1 ≤ m) (hmk : m + 1 ≤ k)
    (h : (∑ ℓ ∈ Finset.Icc 1 m, (k - ℓ)) * ((∑ ℓ ∈ Finset.Icc 1 m, (k - ℓ)) + 1) ≤
      m * (m + 1) * (N - 1)) :
    ((k : ℝ) - (m + 1) / 2) ^ 2 * m ≤ (m + 1) * N := by
  have hle : m * (m + 1) ≤ 2 * m * k := by nlinarith
  have h2 := congrArg (Nat.cast : ℕ → ℝ) (Finset.two_mul_sum_Icc_sub hmk)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_sub hle] at h2
  have hR : ((∑ ℓ ∈ Finset.Icc 1 m, (k - ℓ) : ℕ) : ℝ) *
      (((∑ ℓ ∈ Finset.Icc 1 m, (k - ℓ) : ℕ) : ℝ) + 1) ≤ m * (m + 1) * ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hN : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  set S : ℝ := ((∑ ℓ ∈ Finset.Icc 1 m, (k - ℓ) : ℕ) : ℝ) with hS
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hSe : S = m * ((k : ℝ) - (m + 1) / 2) := by linarith
  have h3 : S ^ 2 ≤ m * (m + 1) * N := by
    nlinarith [mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ m * (m + 1))]
  rw [hSe] at h3
  have : (m : ℝ) * (((k : ℝ) - (m + 1) / 2) ^ 2 * m) ≤ m * ((m + 1) * N) := by nlinarith
  exact le_of_mul_le_mul_left this hmR

/-- L2 (real bounding step): from the integer inequality for every admissible `m`, derive the
real bound `k ≤ √N + N ^ (1 / 4) + 1`. -/
theorem Finset.lindstrom_real_of_count {k N : ℕ}
    (h : ∀ m, 1 ≤ m → m + 1 ≤ k →
      (∑ ℓ ∈ Finset.Icc 1 m, (k - ℓ)) * ((∑ ℓ ∈ Finset.Icc 1 m, (k - ℓ)) + 1) ≤
        m * (m + 1) * (N - 1)) :
    (k : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hq0 : 0 ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · by_contra hcon
    have hk : 2 ≤ k := by
      by_contra hk2
      have : (k : ℝ) ≤ 1 := by exact_mod_cast (by omega : k ≤ 1)
      simp at hcon
      linarith
    have h1 := h 1 le_rfl (by omega)
    simp at h1
    omega
  · set s := Real.sqrt N with hs
    set q := (N : ℝ) ^ (4⁻¹ : ℝ) with hq
    have hqpos : 0 < q := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
    have hqs : q ^ 2 = s := by
      rw [hq, hs, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Real.sqrt_eq_rpow]
      norm_num
    have hss : s ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
    set m := ⌈q⌉₊ with hmdef
    have hm : 1 ≤ m := Nat.ceil_pos.mpr hqpos
    have hqm : q ≤ m := Nat.le_ceil q
    have hmq : (m : ℝ) < q + 1 := Nat.ceil_lt_add_one hq0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    by_cases hkm : k ≤ m
    · have : (k : ℝ) ≤ m := by exact_mod_cast hkm
      linarith
    · have hmk : m + 1 ≤ k := by omega
      have key := lindstrom_sq_bound hm hmk (h m hm hmk)
      set x : ℝ := (k : ℝ) - (m + 1) / 2 with hx
      have hx2 : 2 * m * x ≤ s * (2 * m + 1) := by
        by_contra hcon
        push Not at hcon
        have hrhs : 0 ≤ s * (2 * m + 1) := by positivity
        have hlt : (s * (2 * m + 1)) ^ 2 < (2 * m * x) ^ 2 := by gcongr
        have e1 : (s * (2 * m + 1)) ^ 2 = N * (2 * m + 1) ^ 2 := by rw [mul_pow, hss]
        have e2 : (2 * m * x) ^ 2 = 4 * m * (x ^ 2 * m) := by ring
        have h4 := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 4 * m)
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        nlinarith
      have hqq : q * q ≤ q * m := mul_le_mul_of_nonneg_left hqm hq0
      have hx3 : 2 * m * x ≤ 2 * m * (s + q / 2) := by nlinarith
      have hx4 : x ≤ s + q / 2 := le_of_mul_le_mul_left hx3 (by positivity)
      linarith

namespace Finset

/-- Lindström's bound for a Sidon subset of `Icc 1 N`. -/
theorem IsSidon.card_le_lindstrom {A : Finset ℕ} (hS : IsSidon (A : Set ℕ)) {N : ℕ}
    (hA : A ⊆ Icc 1 N) :
    (#A : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 :=
  lindstrom_real_of_count fun _ hm hmk ↦ hS.lindstrom_count hA hm hmk

/-- Lindström's bound for the maximum size of a Sidon set in `{1, …, N}` [Li69]. -/
theorem maxSidonSubsetCard_Icc_le_lindstrom (N : ℕ) :
    (maxSidonSubsetCard (Icc 1 N) : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  unfold maxSidonSubsetCard
  have hne : ((Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)).Nonempty :=
    ⟨∅, by simp [IsSidon]⟩
  obtain ⟨B, hB, hBeq⟩ := exists_mem_eq_sup _ hne (fun B : Finset ℕ ↦ #B)
  rw [hBeq]
  simp only [mem_filter, mem_powerset] at hB
  exact hB.2.card_le_lindstrom hB.1

end Finset
