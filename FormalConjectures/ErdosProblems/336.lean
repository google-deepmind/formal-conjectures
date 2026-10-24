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
# Erdős Problem 336

*References:*
- [erdosproblems.com/336](https://www.erdosproblems.com/336)
- [ErGr80b] Erdős, P. and Graham, R. L., *On bases with an exact order*.
  Acta Arith. (1980), 201-207.
- [Gr88] Grekos, Georges, *Sur l'ordre d'une base additive*. ([1988?]), Exp. No. 31, 13.
- [Na93] Nash, John C. M., *Some applications of a theorem of M. Kneser*.
  J. Number Theory (1993), 1-8.
-/

@[expose] public section

namespace Erdos336

/-! ## Part 1. Definitions and problem statement -/

/-- `n` is a sum of exactly `k` (not necessarily distinct) elements of `A`. -/
def IsSumOf (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, Multiset.card s = k ∧ (∀ x ∈ s, x ∈ A) ∧ s.sum = n

/-- Every sufficiently large natural number is a sum of exactly `k` elements of `A`. -/
def EventuallyExactly (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsSumOf A k n

/-- `A` is a basis of order `r` in the sense of the source: every sufficiently
large natural number is a sum of at most `r` elements of `A`. -/
def IsBasisOfOrder (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ j ≤ r, IsSumOf A j n

/-- `A` has exact order `k`: `k` is the least number such that every sufficiently
large natural number is a sum of exactly `k` elements of `A`. -/
def HasExactOrder (A : Set ℕ) (k : ℕ) : Prop :=
  EventuallyExactly A k ∧ ∀ j < k, ¬ EventuallyExactly A j

/-- The exact order `k` is realised by some basis of order `r`. -/
def Admissible (r k : ℕ) : Prop :=
  ∃ A : Set ℕ, IsBasisOfOrder A r ∧ HasExactOrder A k

/-- `h` is the function `h(r)` of the problem: for every `r ≥ 2`, `h r` is the
maximum (attained, hence finite) of all admissible exact orders. -/
def IsH336 (h : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 2 ≤ r → IsGreatest {k | Admissible r k} (h r)

/-- **The open problem, with the answer as a parameter.**
`Erdos336Answer c` says: `h(r)` is well defined for every `r ≥ 2` (the maximum
exists), and `h(r)/r² → c`. "Find the value of the limit" asks for the `c` with
`Erdos336Answer c`. -/
def Erdos336Answer (c : ℝ) : Prop :=
  (∃ h : ℕ → ℕ, IsH336 h) ∧
    ∀ h : ℕ → ℕ, IsH336 h →
      Filter.Tendsto (fun r : ℕ => (h r : ℝ) / (r : ℝ) ^ 2) Filter.atTop (nhds c)

/--
For $r\geq 2$ let $h(r)$ be the maximal finite $k$ such that there exists a basis
$A\subseteq \mathbb{N}$ of order $r$ (so every large integer is the sum of at most $r$
integers from $A$) and exact order $k$ (so every large integer is the sum of exactly $k$
integers from $A$).

Find the value of $\lim_r \frac{h(r)}{r^2}$.

Exact order means the least such $k$. `IsH336` requires an attained maximum for every
$r \geq 2$, and `Erdos336Answer` includes its existence to avoid a vacuous limit statement.
-/
@[category research open, AMS 5 11]
theorem erdos_336 : Erdos336Answer answer(sorry) := by
  sorry

/-- The best known bounds are $1/3 \leq \liminf_r h(r)/r^2$ and
$\limsup_r h(r)/r^2 \leq 1/2$. The lower bound is due to Grekos [Gr88],
and the upper bound to Nash [Na93]. -/
@[category research solved, AMS 5 11]
theorem erdos_336.variants.known_bounds :
    (∃ h : ℕ → ℕ, IsH336 h) ∧
      ∀ h : ℕ → ℕ, IsH336 h → ∀ ε > (0 : ℝ), ∀ᶠ r : ℕ in Filter.atTop,
        1 / 3 - ε ≤ (h r : ℝ) / (r : ℝ) ^ 2 ∧
          (h r : ℝ) / (r : ℝ) ^ 2 ≤ 1 / 2 + ε := by
  sorry

/-! ## Part 2. Basic facts about the definitions -/

/-- Adding one element of `A` to a `k`-term representation. -/
@[category API, AMS 5 11]
lemma IsSumOf.cons {A : Set ℕ} {k n a : ℕ} (h : IsSumOf A k n) (ha : a ∈ A) :
    IsSumOf A (k + 1) (a + n) := by
  obtain ⟨s, hc, hm, hs⟩ := h
  refine ⟨a ::ₘ s, by simp [hc], ?_, by simp [hs]⟩
  intro x hx
  rcases Multiset.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact hm x hx

/-- One step of upward closure. -/
@[category API, AMS 5 11]
lemma eventuallyExactly_succ {A : Set ℕ} {k a : ℕ} (ha : a ∈ A)
    (h : EventuallyExactly A k) : EventuallyExactly A (k + 1) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + a, fun n hn => ?_⟩
  have := (hN (n - a) (by omega)).cons ha
  rwa [show a + (n - a) = n by omega] at this

/-- "Every large integer is a sum of exactly `k` elements of `A`" is upward closed
in `k` (for nonempty `A`). This is why exact order must mean the *least* such `k`. -/
@[category API, AMS 5 11]
lemma eventuallyExactly_mono {A : Set ℕ} (hA : A.Nonempty) {j k : ℕ} (hjk : j ≤ k)
    (h : EventuallyExactly A j) : EventuallyExactly A k := by
  obtain ⟨a, ha⟩ := hA
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact eventuallyExactly_succ ha ih

/-- The exact order is unique. -/
@[category API, AMS 5 11]
lemma HasExactOrder.unique {A : Set ℕ} {k k' : ℕ} (h : HasExactOrder A k)
    (h' : HasExactOrder A k') : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2 k hlt h.1
  · exact h.2 k' hlt h'.1

/-- The function `h(r)` is uniquely determined (for `r ≥ 2`) when it exists. -/
@[category API, AMS 5 11]
lemma IsH336.unique {h₁ h₂ : ℕ → ℕ} (H₁ : IsH336 h₁) (H₂ : IsH336 h₂) {r : ℕ}
    (hr : 2 ≤ r) : h₁ r = h₂ r :=
  le_antisymm ((H₂ r hr).2 (H₁ r hr).1) ((H₁ r hr).2 (H₂ r hr).1)

/-! ## Part 3. The example on the problem page: order 2, exact order 3 -/

/-- `A = ⋃_{k ≥ 0} (2^{2k}, 2^{2k+1}]`. -/
def exampleSet : Set ℕ := {n | ∃ k : ℕ, 2 ^ (2 * k) < n ∧ n ≤ 2 ^ (2 * k + 1)}

@[category API, AMS 5 11]
lemma mem_exampleSet {n : ℕ} : n ∈ exampleSet ↔ ∃ k : ℕ, 4 ^ k < n ∧ n ≤ 2 * 4 ^ k := by
  simp only [exampleSet, Set.mem_ofPred_eq, pow_succ, pow_mul]
  norm_num [mul_comm]

@[category API, AMS 5 11]
lemma two_le_of_mem {n : ℕ} (h : n ∈ exampleSet) : 2 ≤ n := by
  obtain ⟨k, h1, -⟩ := mem_exampleSet.1 h
  have := Nat.one_le_pow k 4 (by norm_num)
  omega

/-- An element of $A$ below $4^{m+1}$ is at most $2 \cdot 4^m$. -/
@[category API, AMS 5 11]
lemma le_of_mem_of_lt {x m : ℕ} (hx : x ∈ exampleSet) (hlt : x < 4 ^ (m + 1)) :
    x ≤ 2 * 4 ^ m := by
  obtain ⟨j, h1, h2⟩ := mem_exampleSet.1 hx
  have hj : j ≤ m := by
    by_contra hj
    have : 4 ^ (m + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 4 ^ j ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hj
  omega

@[category API, AMS 5 11]
lemma isSumOf_one {A : Set ℕ} {a : ℕ} (ha : a ∈ A) : IsSumOf A 1 a :=
  ⟨{a}, by simp, by simpa using ha, by simp⟩

@[category API, AMS 5 11]
lemma isSumOf_two {A : Set ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    IsSumOf A 2 (a + b) := by
  simpa using (isSumOf_one hb).cons ha

/-- Every `n ∈ [4^k + 3, 4^(k+1)]` with `k ≥ 1` is a sum of exactly two elements
of `A`. -/
@[category API, AMS 5 11]
lemma isSumOf_two_of_mem_Icc {k n : ℕ} (hk : 1 ≤ k) (h1 : 4 ^ k + 3 ≤ n)
    (h2 : n ≤ 4 ^ (k + 1)) : IsSumOf exampleSet 2 n := by
  have hP : 4 ≤ 4 ^ k := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [pow_succ] at h2
  have h2mem : (2 : ℕ) ∈ exampleSet := mem_exampleSet.2 ⟨0, by norm_num⟩
  rcases lt_or_ge n (2 * 4 ^ k + 1) with h | h
  · -- `n = 2 + (n - 2)` with `n - 2 ∈ (4^k, 2·4^k]`
    have : n - 2 ∈ exampleSet := mem_exampleSet.2 ⟨k, by omega, by omega⟩
    simpa [show 2 + (n - 2) = n by omega] using isSumOf_two h2mem this
  rcases eq_or_lt_of_le h with h | h
  · -- `n = 2 + (2·4^k - 1)`
    have : 2 * 4 ^ k - 1 ∈ exampleSet := mem_exampleSet.2 ⟨k, by omega, by omega⟩
    simpa [show 2 + (2 * 4 ^ k - 1) = n by omega] using isSumOf_two h2mem this
  · -- halves
    have ha : n / 2 ∈ exampleSet := mem_exampleSet.2 ⟨k, by omega, by omega⟩
    have hb : n - n / 2 ∈ exampleSet := mem_exampleSet.2 ⟨k, by omega, by omega⟩
    simpa [show n / 2 + (n - n / 2) = n by omega] using isSumOf_two ha hb

/-- `A` is a basis of order `2`: every `n ≥ 4` is a sum of at most two elements. -/
@[category API, AMS 5 11]
theorem exampleSet_isBasisOfOrder_two : IsBasisOfOrder exampleSet 2 := by
  refine ⟨4, fun n hn => ?_⟩
  set k := Nat.log 4 (n - 1)
  have hlo : 4 ^ k ≤ n - 1 := Nat.pow_log_le_self 4 (by omega)
  have hhi : n - 1 < 4 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hk1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rcases le_or_gt n (2 * 4 ^ k) with h | h
  · exact ⟨1, by norm_num, isSumOf_one (mem_exampleSet.2 ⟨k, by omega, h⟩)⟩
  · refine ⟨2, le_rfl, ?_⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · -- `k = 0`, so `n = 4 = 2 + 2`
      rw [hk0] at hlo hhi h
      have h2mem : (2 : ℕ) ∈ exampleSet := mem_exampleSet.2 ⟨0, by norm_num⟩
      simpa [show n = 2 + 2 by norm_num at hlo hhi h; omega] using isSumOf_two h2mem h2mem
    · exact isSumOf_two_of_mem_Icc hk0 (by omega) (by omega)

/-- `4^m + 1` (`m ≥ 1`) is not a sum of exactly two elements of `A`. -/
@[category API, AMS 5 11]
lemma not_isSumOf_two_pow_add_one (m : ℕ) : ¬ IsSumOf exampleSet 2 (4 ^ (m + 1) + 1) := by
  rintro ⟨s, hc, hm, hs⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, s = {a, b} := Multiset.card_eq_two.1 hc
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
    forall_eq_or_imp, forall_eq, Multiset.sum_cons, Multiset.sum_singleton] at hm hs
  have ha2 := two_le_of_mem hm.1
  have hb2 := two_le_of_mem hm.2
  have ha := le_of_mem_of_lt hm.1 (m := m) (by omega)
  have hb := le_of_mem_of_lt hm.2 (m := m) (by omega)
  rw [pow_succ] at hs
  omega

/-- `4^m` (`m ≥ 1`) is not in `A`. -/
@[category API, AMS 5 11]
lemma pow_not_mem (m : ℕ) : 4 ^ (m + 1) ∉ exampleSet := by
  intro h
  obtain ⟨j, h1, h2⟩ := mem_exampleSet.1 h
  rcases le_or_gt j m with hj | hj
  · have : 4 ^ j ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hj
    rw [pow_succ] at h2
    have : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
    omega
  · have : 4 ^ (m + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega

@[category API, AMS 5 11]
lemma exists_pow_ge (N : ℕ) : ∃ m : ℕ, N ≤ 4 ^ (m + 1) :=
  ⟨N, by
    have := Nat.lt_pow_self (show 1 < 4 by norm_num) (n := N)
    calc N ≤ 4 ^ N := this.le
      _ ≤ 4 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)⟩

@[category API, AMS 5 11]
lemma exists_pow_add_one_ge (N : ℕ) : ∃ m : ℕ, N ≤ 4 ^ (m + 1) + 1 := by
  obtain ⟨m, hm⟩ := exists_pow_ge N
  exact ⟨m, by omega⟩

/-- `A` is not a sum of exactly two elements eventually. -/
@[category API, AMS 5 11]
lemma exampleSet_not_eventuallyExactly_two : ¬ EventuallyExactly exampleSet 2 := by
  rintro ⟨N, hN⟩
  obtain ⟨m, hm⟩ := exists_pow_add_one_ge N
  exact not_isSumOf_two_pow_add_one m (hN _ hm)

/-- Every `n ≥ 10` is a sum of exactly three elements of `A`. -/
@[category API, AMS 5 11]
lemma exampleSet_eventuallyExactly_three : EventuallyExactly exampleSet 3 := by
  refine ⟨10, fun n hn => ?_⟩
  set k := Nat.log 4 (n - 5)
  have hlo : 4 ^ k ≤ n - 5 := Nat.pow_log_le_self 4 (by omega)
  have hhi : n - 5 < 4 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hk0 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this] at hhi
    omega
  have hP : 4 ≤ 4 ^ k := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk0
  have hpow : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
  have h2mem : (2 : ℕ) ∈ exampleSet := mem_exampleSet.2 ⟨0, by norm_num⟩
  have h5mem : (5 : ℕ) ∈ exampleSet := mem_exampleSet.2 ⟨1, by norm_num⟩
  rcases le_or_gt (n - 2) (4 ^ (k + 1)) with h | h
  · have := (isSumOf_two_of_mem_Icc hk0 (n := n - 2) (by omega) h).cons h2mem
    simpa [show 2 + (n - 2) = n by omega] using this
  · have := (isSumOf_two_of_mem_Icc hk0 (n := n - 5) (by omega) (by omega)).cons h5mem
    simpa [show 5 + (n - 5) = n by omega] using this

/-- The set $A = \bigcup_{k \geq 0} (2^{2k}, 2^{2k+1}]$ has order $2$ and exact
order $3$. It is not a basis of order $1$. -/
@[category test, AMS 5 11]
theorem exampleSet_order_two_exactOrder_three :
    IsBasisOfOrder exampleSet 2 ∧ ¬ IsBasisOfOrder exampleSet 1 ∧
      HasExactOrder exampleSet 3 := by
  refine ⟨exampleSet_isBasisOfOrder_two, ?_, exampleSet_eventuallyExactly_three, ?_⟩
  · rintro ⟨N, hN⟩
    obtain ⟨m, hm⟩ := exists_pow_ge N
    obtain ⟨j, hj, s, hc, hmem, hs⟩ := hN _ hm
    interval_cases j
    · rw [Multiset.card_eq_zero] at hc
      subst hc
      simp only [Multiset.sum_zero] at hs
      exact absurd hs.symm (pow_ne_zero _ (by norm_num))
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hc
      simp only [Multiset.mem_singleton, forall_eq, Multiset.sum_singleton] at hmem hs
      exact pow_not_mem m (hs ▸ hmem)
  · intro j hj h
    exact exampleSet_not_eventuallyExactly_two
      (eventuallyExactly_mono ⟨2, mem_exampleSet.2 ⟨0, by norm_num⟩⟩ (by omega) h)

/-- Consequence: the exact order `3` is admissible for `r = 2`, so `h(2) ≥ 3`
whenever `h` exists. (The known value is `h(2) = 4`, Erdős–Graham.) -/
@[category API, AMS 5 11]
theorem admissible_two_three : Admissible 2 3 :=
  ⟨exampleSet, exampleSet_order_two_exactOrder_three.1,
    exampleSet_order_two_exactOrder_three.2.2⟩

@[category API, AMS 5 11]
theorem three_le_h_two {h : ℕ → ℕ} (H : IsH336 h) : 3 ≤ h 2 :=
  (H 2 le_rfl).2 admissible_two_three

end Erdos336
