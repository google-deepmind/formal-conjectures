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

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Greedy Stanley sequences with a two-element seed

This module constructs the Stanley sequence with seed $\{0, n\}$ for $n>0$,
proves uniqueness, and bounds its terms by $n+(k - 1)(k+2)/2$.

*References:*
- [Moy, On the Growth of the Counting Function of Stanley Sequences](https://arxiv.org/abs/1101.0022v3)
- [Erdős Problem 271](https://www.erdosproblems.com/271)
- [van Doorn and Sothanaphan's explicit bound](https://www.erdosproblems.com/forum/thread/271)
-/

@[expose] public section

namespace StanleySequence

/-- Values completing a nonconstant three-term progression with two members. -/
def forbidden (s : Finset ℕ) : Finset ℕ :=
  ((s ×ˢ s).filter fun p => p.1 < p.2).image fun p => 2 * p.2 - p.1

lemma mem_forbidden {s : Finset ℕ} {m : ℕ} :
    m ∈ forbidden s ↔ ∃ x ∈ s, ∃ y ∈ s, x < y ∧ 2 * y - x = m := by
  simp only [forbidden, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxy⟩, hm⟩
    exact ⟨x, hx, y, hy, hxy, hm⟩
  · rintro ⟨x, hx, y, hy, hxy, hm⟩
    exact ⟨(x, y), ⟨⟨hx, hy⟩, hxy⟩, hm⟩

lemma exists_next (s : Finset ℕ) : ∃ m : ℕ, s.sup id < m ∧ m ∉ forbidden s := by
  refine ⟨2 * s.sup id + 1, by omega, ?_⟩
  intro hm
  obtain ⟨x, hx, y, hy, hxy, he⟩ := mem_forbidden.mp hm
  have hb : y ≤ s.sup id := Finset.le_sup (f := id) hy
  omega

/-- The least admissible integer strictly above every member of s. -/
def next (s : Finset ℕ) : ℕ := Nat.find (exists_next s)

lemma next_spec (s : Finset ℕ) : s.sup id < next s ∧ next s ∉ forbidden s :=
  Nat.find_spec (exists_next s)

lemma next_le {s : Finset ℕ} {m : ℕ}
    (hm : s.sup id < m) (hf : m ∉ forbidden s) : next s ≤ m :=
  Nat.find_min' (exists_next s) ⟨hm, hf⟩

/-- The Stanley sequence with seed {0, n}. Theorems about it require 0<n. -/
def a (n k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then n else
    next ((Finset.univ : Finset (Fin k)).image fun i => a n i.val)
termination_by k

/-- The first k terms, with indices 0, ..., k - 1. -/
def initialSegment (n k : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin k)).image fun i => a n i.val

@[simp] theorem a_zero (n : ℕ) : a n 0 = 0 := by rw [a]; simp
@[simp] theorem a_one (n : ℕ) : a n 1 = n := by rw [a]; simp

lemma a_eq_next (n : ℕ) {k : ℕ} (hk : 2 ≤ k) : a n k = next (initialSegment n k) := by
  rw [a]
  simp [show k ≠ 0 by omega, show k ≠ 1 by omega, initialSegment]

lemma mem_initialSegment {n k x : ℕ} :
    x ∈ initialSegment n k ↔ ∃ i < k, a n i = x := by
  simp only [initialSegment, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, hi⟩, he⟩

lemma a_mem_initialSegment (n : ℕ) {i k : ℕ} (hi : i < k) : a n i ∈ initialSegment n k :=
  mem_initialSegment.mpr ⟨i, hi, rfl⟩

theorem a_strictMono {n : ℕ} (hn : 0 < n) : StrictMono (a n) := by
  intro i j hij
  by_cases hj : j = 1
  · have hi : i = 0 := by omega
    simp [hj, hi, hn]
  · have h2 : 2 ≤ j := by omega
    rw [a_eq_next n h2]
    exact lt_of_le_of_lt (Finset.le_sup (f := id) (a_mem_initialSegment n hij))
      (next_spec (initialSegment n j)).1

lemma initialSegment_sup {n k : ℕ} (hn : 0 < n) : (initialSegment n (k + 1)).sup id = a n k := by
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_initialSegment.mp hx
    exact (a_strictMono hn).monotone (by omega)
  · exact Finset.le_sup (f := id) (a_mem_initialSegment n (by omega))

/-- No three terms at strictly increasing indices form an arithmetic progression. -/
theorem no_three_term_AP {n : ℕ} (hn : 0 < n) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) : a n i + a n k ≠ 2 * a n j := by
  intro he
  have hk : 2 ≤ k := by omega
  have hfree := (next_spec (initialSegment n k)).2
  rw [← a_eq_next n hk] at hfree
  apply hfree
  apply mem_forbidden.mpr
  refine ⟨a n i, a_mem_initialSegment n (by omega), a n j, a_mem_initialSegment n hjk,
    a_strictMono hn hij, ?_⟩
  omega

/-- Every admissible candidate above $a_k$ is at least $a_{k+1}$. -/
theorem greedy_minimum {n k m : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (hm : a n k < m) (hf : m ∉ forbidden (initialSegment n (k + 1))) : a n (k + 1) ≤ m := by
  rw [a_eq_next n (by omega)]
  exact next_le (by rwa [initialSegment_sup hn]) hf

/-- Each skipped integer above the seed is covered by a pair of earlier terms. -/
lemma skipped_is_forbidden {n k m : ℕ} (hn : 0 < n)
    (hmn : n < m) (hmk : m < a n k) (hnot : m ∉ initialSegment n k) :
    m ∈ forbidden (initialSegment n k) := by
  let j := Nat.find (show ∃ j, m < a n j from ⟨k, hmk⟩)
  have hj : m < a n j := Nat.find_spec (show ∃ j, m < a n j from ⟨k, hmk⟩)
  have hjk : j ≤ k := Nat.find_min' (show ∃ j, m < a n j from ⟨k, hmk⟩) hmk
  have hj0 : j ≠ 0 := by intro he; simp [he] at hj
  have hj1 : j ≠ 1 := by intro he; simp [he] at hj; omega
  have h2 : 2 ≤ j := by omega
  have hprev : a n (j - 1) ≤ m := by
    exact le_of_not_gt (Nat.find_min (show ∃ j, m < a n j from ⟨k, hmk⟩) (by omega))
  have hprevlt : a n (j - 1) < m := by
    apply lt_of_le_of_ne hprev
    intro he
    apply hnot
    exact mem_initialSegment.mpr ⟨j - 1, by omega, he⟩
  have hbad : m ∈ forbidden (initialSegment n j) := by
    by_contra hgood
    have hb := greedy_minimum hn (show 1 ≤ j - 1 by omega) hprevlt
      (show m ∉ forbidden (initialSegment n ((j - 1) + 1)) by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hgood)
    have hje : j - 1 + 1 = j := by omega
    rw [hje] at hb
    omega
  obtain ⟨x, hx, y, hy, hxy, he⟩ := mem_forbidden.mp hbad
  obtain ⟨i, hi, rfl⟩ := mem_initialSegment.mp hx
  obtain ⟨l, hl, rfl⟩ := mem_initialSegment.mp hy
  exact mem_forbidden.mpr ⟨a n i, a_mem_initialSegment n (by omega),
    a n l, a_mem_initialSegment n (by omega), hxy, he⟩

lemma initialSegment_card {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (initialSegment n k).card = k := by
  have hi : Function.Injective (fun i : Fin k => a n i.val) := by
    intro i j he
    exact Fin.ext ((a_strictMono hn).injective he)
  rw [initialSegment, Finset.card_image_of_injective _ hi]
  simp

lemma forbidden_card_le (s : Finset ℕ) : (forbidden s).card ≤ s.card.choose 2 := by
  unfold forbidden
  exact (Finset.card_image_le).trans (by rw [Finset.card_product_filter_lt])

/-- Counting all accepted and rejected candidates up to $a_k$. -/
theorem counting_bound {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) :
    a n k - n ≤ (k - 1) + k.choose 2 := by
  let t := ((initialSegment n (k + 1)).erase 0).erase n
  have hz : 0 ∈ initialSegment n (k + 1) := by
    simpa using a_mem_initialSegment n (show 0 < k + 1 by omega)
  have hnm : n ∈ (initialSegment n (k + 1)).erase 0 := by
    apply Finset.mem_erase.mpr
    refine ⟨by omega, ?_⟩
    simpa using a_mem_initialSegment n (show 1 < k + 1 by omega)
  have htc : t.card = k - 1 := by
    simp only [t, Finset.card_erase_of_mem hnm, Finset.card_erase_of_mem hz,
      initialSegment_card hn]
    omega
  have hcover : Finset.Ioc n (a n k) ⊆ t ∪ forbidden (initialSegment n k) := by
    intro m hm
    obtain ⟨hmn, hmk⟩ := Finset.mem_Ioc.mp hm
    by_cases hin : m ∈ initialSegment n (k + 1)
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega, hin⟩⟩
    · apply Finset.mem_union.mpr
      right
      have hne : m ≠ a n k := by
        intro he
        apply hin
        rw [he]
        exact a_mem_initialSegment n (by omega)
      apply skipped_is_forbidden hn hmn (by omega)
      intro hp
      obtain ⟨i, hi, he⟩ := mem_initialSegment.mp hp
      exact hin (mem_initialSegment.mpr ⟨i, by omega, he⟩)
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [Nat.card_Ioc, htc] at hc
  have hf := forbidden_card_le (initialSegment n k)
  rw [initialSegment_card hn] at hf
  omega

/-- Explicit bound, written without subtraction in the natural numbers. -/
theorem explicit_bound_nat {n : ℕ} (hn : 0 < n) (k : ℕ) :
    2 * a n k + 2 ≤ 2 * n + k * (k + 1) := by
  by_cases hk : k = 0
  · simp [hk]; omega
  have hk1 : 1 ≤ k := by omega
  have hnk : n ≤ a n k := by
    simpa using (a_strictMono hn).monotone hk1
  have hc := counting_bound hn hk1
  have he : 2 * k.choose 2 ≤ k * (k - 1) := by
    rw [Nat.choose_two_right]
    omega
  have hsub : k * (k - 1) + k = k * k := by
    have he' : k - 1 + 1 = k := by omega
    nlinarith
  have hkn : k - 1 + 1 = k := by omega
  have han : a n k - n + n = a n k := Nat.sub_add_cancel hnk
  nlinarith

/-- The exact formula printed in the source, with real-valued arithmetic. -/
theorem explicit_bound {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (a n k : ℝ) ≤ (n : ℝ) + ((k : ℝ) - 1) * ((k : ℝ) + 2) / 2 := by
  have h := explicit_bound_nat hn k
  have hr : 2 * (a n k : ℝ) + 2 ≤ 2 * (n : ℝ) + (k : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast h
  nlinarith

/-- A specification using only the mathematical seed, AP condition, and greediness. -/
structure IsStanley (n : ℕ) (b : ℕ → ℕ) : Prop where
  zero_eq : b 0 = 0
  one_eq : b 1 = n
  increasing : StrictMono b
  noAP : ∀ i j k, i < j → j < k → b i + b k ≠ 2 * b j
  greedy : ∀ k m, 1 ≤ k → b k < m →
    (∀ i j, i < j → j ≤ k → b i + m ≠ 2 * b j) → b (k + 1) ≤ m

/-- The constructed sequence satisfies the source's mathematical definition. -/
theorem a_isStanley {n : ℕ} (hn : 0 < n) : IsStanley n (a n) where
  zero_eq := a_zero n
  one_eq := a_one n
  increasing := a_strictMono hn
  noAP := fun _ _ _ hij hjk => no_three_term_AP hn hij hjk
  greedy := by
    intro k m hk hm hfree
    apply greedy_minimum hn hk hm
    intro hbad
    obtain ⟨x, hx, y, hy, hxy, he⟩ := mem_forbidden.mp hbad
    obtain ⟨i, hi, rfl⟩ := mem_initialSegment.mp hx
    obtain ⟨j, hj, rfl⟩ := mem_initialSegment.mp hy
    have hij : i < j := (a_strictMono hn).lt_iff_lt.mp hxy
    have hne := hfree i j hij (by omega)
    apply hne
    omega

/-- The seed and mathematical greedy rule determine the sequence uniquely. -/
theorem uniqueness {n : ℕ} (hn : 0 < n) {b : ℕ → ℕ} (hb : IsStanley n b) :
    b = a n := by
  funext t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht0 : t = 0
    · simp [ht0, hb.zero_eq]
    by_cases ht1 : t = 1
    · simp [ht1, hb.one_eq]
    have ht2 : 2 ≤ t := by omega
    let r := t - 1
    have hr : 1 ≤ r := by omega
    have hrt : r < t := by omega
    have he : r + 1 = t := by omega
    apply le_antisymm
    · have hmin : b (r + 1) ≤ a n t := by
        apply hb.greedy r (a n t) hr
        · rw [ih r hrt]
          exact a_strictMono hn hrt
        · intro i j hij hjr
          have hjt : j < t := by omega
          have hit : i < t := by omega
          rw [ih i hit, ih j hjt]
          exact no_three_term_AP hn hij hjt
      simpa [he] using hmin
    · have hmin : a n (r + 1) ≤ b t := by
        apply greedy_minimum hn hr
        · rw [← ih r hrt]
          exact hb.increasing hrt
        · rw [he]
          intro hbad
          obtain ⟨x, hx, y, hy, hxy, hval⟩ := mem_forbidden.mp hbad
          obtain ⟨i, hi, rfl⟩ := mem_initialSegment.mp hx
          obtain ⟨j, hj, rfl⟩ := mem_initialSegment.mp hy
          have hij : i < j := (a_strictMono hn).lt_iff_lt.mp hxy
          have hne := hb.noAP i j t hij hj
          rw [ih i hi, ih j hj] at hne
          apply hne
          omega
      simpa [he] using hmin

/-- Existence and uniqueness of the Stanley sequence starting with 0, n. -/
theorem exists_unique_stanley {n : ℕ} (hn : 0 < n) :
    ∃! b : ℕ → ℕ, IsStanley n b := by
  exact ⟨a n, a_isStanley hn, fun _ hb => uniqueness hn hb⟩

/-- The explicit bound applies to any sequence satisfying the mathematical rule. -/
theorem explicit_bound_of_isStanley {n : ℕ} (hn : 0 < n)
    {b : ℕ → ℕ} (hb : IsStanley n b) (k : ℕ) :
    (b k : ℝ) ≤ (n : ℝ) + ((k : ℝ) - 1) * ((k : ℝ) + 2) / 2 := by
  rw [uniqueness hn hb]
  exact explicit_bound hn k

end StanleySequence
