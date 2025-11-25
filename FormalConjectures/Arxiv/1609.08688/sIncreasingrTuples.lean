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

import FormalConjectures.Util.ProblemImports

/-! # The length of an $s$-increasing sequence of $r$-tuples

This file contains the formalisation of [GoLo21] up to and
including Conjecture 1.8

[GoLo21] W.T. Gowers and J. Long, _The length of an $s$-increasing sequence of $r$-tuples_,
Combinatorics, Probability and Computing (2021), 686-721.

*References:*
 - [arxiv/1609.08688](https://arxiv.org/abs/1609.08688) **The length of an $s$-increasing sequence of $r$-tuples** by *W. T. Gowers, J. Long*
 - [GoLo21]( https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/length-of-an-sincreasing-sequence-of-rtuples/7301418D47DB1ECD6BE71C20E8A98D0A) **The length of an $s$-increasing sequence of $r$-tuples** by *W. T. Gowers, J. Long*, 2021
-/

namespace Arxiv.«1609.08688»

/--
Let $a = (a_1, a_2, a_3)$ and $b = (b_1, b_2, b_3)$ be two triples of integers.
Say that $a$ is $2$-less than $b$, or $a <_2 b$, if $a_i < b_i$ for at least
two co-ordinates $i$.
-/
def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

@[simp, category API, AMS 5]
theorem not_lt₂ {α : Type*} [LinearOrder α] {a b : Fin 3 → α} :
    ¬a <₂ b ↔ ∀ i j, i ≠ j → a i < b i → b j ≤ a j := by simp [lt₂]

@[category API, AMS 5]
theorem not_lt₂_of_forall_le {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (h : ∀ i, b i ≤ a i) : ¬a <₂ b := not_lt₂.2 fun _ _ _ _ => h _

@[category API, AMS 5]
theorem not_lt₂_of_exists {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (i j : Fin 3) (hij : i ≠ j) (hi : b i ≤ a i) (hj : b j ≤ a j) :
    ¬a <₂ b := by
  refine not_lt₂.2 fun k l hkl h => ?_
  have : k ≠ i := fun hk => not_lt.2 hi (hk ▸ h)
  have : k ≠ j := fun hk => not_lt.2 hj (hk ▸ h)
  have : l = i ∨ l = j := by omega
  rcases this with (rfl | rfl); exact hi; exact hj

@[category API, AMS 5]
theorem not_lt₂_self {α : Type*} [LinearOrder α] (a : Fin 3 → α) : ¬a <₂ a := by
  simp

/-- For example, $(3, 3, 9) <_2 (5, 6, 1)$. -/
@[category test, AMS 5]
theorem lt₂_example_1 : ![3, 3, 9] <₂ ![5, 6, 1] := ⟨0, 1, zero_ne_one, by simp⟩

/-- $(5, 6, 1) <_2 (7, 7, 7)$ -/
@[category test, AMS 5]
theorem lt₂_example_2 : ![5, 6, 1] <₂ ![7, 7, 7] := ⟨0, 2, by simp, by simp⟩

/-- $(7, 7, 7) <_2 (7, 8, 9)$ -/
@[category test, AMS 5]
theorem lt₂_example_3 : ![7, 7, 7] <₂ ![7, 8, 9] := ⟨1, 2, by simp, by simp⟩

/-- but $(1, 2, 3)$ is not $2$-less than $(1, 2, 4). -/
@[category test, AMS 5]
theorem not_lt₂_example : ¬![1, 2, 3] <₂ ![1, 2, 4] := not_lt₂_of_exists 0 1 zero_ne_one (by simp) (by simp)

/-- The $2$-less relation is not transitive on the naturals. -/
@[category API, AMS 5]
theorem not_trans_lt₂_nat : ∃ (a b c : Fin 3 → ℕ),
    a <₂ b ∧ b <₂ c ∧ ¬a <₂ c :=
  ⟨![1, 2, 3], ![2, 3, 1], ![3, 1, 2], ⟨0, 1, zero_ne_one, by simp⟩,
     ⟨0, 2, by simp, by simp⟩, not_lt₂_of_exists 1 2 (by simp) (by simp) (by simp)⟩

/--
Since the $2$-less relation is not transitive, we make a further definition to
specify transivity.
-/
def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

@[simp, category API, AMS 5]
theorem isIncreasing₂_nil {α : Type*} [LT α] : IsIncreasing₂ (α := α) [] := by
  simp [IsIncreasing₂]

@[simp, category API, AMS 5]
theorem isIncreasing₂_singleton {α : Type*} [LT α] (a : Fin 3 → α) : IsIncreasing₂ [a] := by
  simp [IsIncreasing₂]

@[category API, AMS 5]
theorem isIncreasing₂_const_length {α : Type*} [LinearOrder α] {val : α} {s : List (Fin 3 → α)}
    (h : IsIncreasing₂ s)
    (h_const : ∀ a ∈ s, ∀ j, a j = val) : s.length < 2 := by
  by_contra!
  have h₀ : s[0] = fun _ => val := funext fun i => by simp [h_const s[0] (by simp)]
  have h₁ : s[1] = fun _ => val := funext fun i => by simp [h_const s[1] (by simp)]
  have := List.pairwise_iff_getElem.1 h 0 1 (by linarith) (by linarith) zero_lt_one
  simp [h₀, h₁] at this
  exact not_lt₂_self _ this

/--
Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with each coordinate
belong to $[n]$ ($= \{1, 2, ..., n\}$).
-/
noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

@[category test, AMS 5]
theorem maximalLength_zero : maximalLength 0 = 0 := by
  have (x : ℕ) (s : List (Fin 3 → ℕ)) :
      IsIncreasing₂ s ∧ (∀ a, a ∉ s) ∧ s.length = x ↔ s = [] ∧ x = 0 := by
    refine ⟨fun ⟨ha₁, ha₂, rfl⟩ => ?_, fun ⟨h₁, h₂⟩ => by simp [h₁, h₂]⟩
    simp only [List.length_eq_zero_iff, and_self]
    refine List.eq_nil_of_subset_nil fun ai hai => ?_
    simpa using ha₂ ai hai
  simp [maximalLength, fun x => exists_congr (this x)]

@[category test, AMS 5]
theorem maximalLength_one : maximalLength 1 = 1 := by
  classical
  have (x : ℕ) (s : List (Fin 3 → ℕ)) :
      IsIncreasing₂ s ∧ (∀ a ∈ s, ∀ i, a i = 1) ∧ s.length = x ↔
        s = [fun _ => 1] ∧ x = 1 ∨ s = [] ∧ x = 0 := by
    refine ⟨fun ⟨hs₁, hs₂, hx⟩ => ?_, fun h => by aesop⟩
    have := hx ▸ isIncreasing₂_const_length hs₁ hs₂
    interval_cases x; simp [List.length_eq_zero_iff.1 hx]; simp
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hx
    simp at hs₂
    rw [show a = fun _ => 1 from funext fun i => by simp [hs₂ i]]
  simp [maximalLength, fun x => exists_congr (this x)]
  erw [Nat.sSup_def ⟨1, by aesop⟩, Nat.find_eq_iff]
  refine ⟨by aesop, fun n hn => ?_⟩
  simp [Nat.lt_one_iff.1 hn]
  exact ⟨1, ⟨[fun _ => 1], by simp⟩, one_ne_zero⟩

@[category test, AMS 5]
theorem maximalLength_four : maximalLength 4 = 8 := by
  sorry

/-- In a set of more than $n^2$ triples with coordinates from $\{1, ..., n\}$ we must
have two triples that are equal in their first two coordinates. -/
@[category API, AMS 5]
lemma exists_pair_of_mem_Icc {s : List (Fin 3 → ℕ)} {n : ℕ} (hn : 2 ≤ n)
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : s.length > n ^ 2) :
    ∃ (i j : Fin s.length), i ≠ j ∧ s[i] 0 = s[j] 0 ∧ s[i] 1 = s[j] 1 := by
  sorry

/-- For all $n$ we have $F(n) \leq n^2$. -/
@[category research solved, AMS 5]
theorem maximalLength_le (n : ℕ) : F n ≤ n ^ 2 := by
  sorry

/-- Moreover, whenever $n$ is a perfect square we have $F(n) \geq n^{3/2}$. -/
@[category research solved, AMS 5]
theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n := by
  sorry

/-- Two triples $t_1$ and $t_2$ are $2$-comparable if one of them is $2$-less
than the other. -/
def IsComparable₂ {α : Type*} [LT α] (t₁ t₂ : Fin 3 → α) : Prop :=
  t₁ <₂ t₂ ∨ t₂ <₂ t₁

/-- A set of triples is $2$-comparable if any two of them are $2$-comparable. -/
def IsComparableSet₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop :=
  ∃ t₁ t₂, t₁ ≠ t₂ ∧ t₁ ∈ s ∧ t₂ ∈ s ∧ IsComparable₂ t₁ t₂

open Filter in
/-- $F(n) \leq n^2 / \exp(\Omega(\log^*(n)))$. -/
@[category research solved, AMS 5]
theorem maximalLength_le_isBigO : ∃ Ω : ℕ → ℝ,
    (fun (n : ℕ) => (Real.iteratedLog n : ℝ)) =O[atTop] Ω ∧
      ∀ n, F n ≤ n ^ 2 / Real.exp (Ω n) := by
  sorry

/-- We define the product of two triples $(a, b, c)$ and $(d, e, f)$ by
$((a, d), (b, e), (c, f))$, where the pairs are arranged in lexicographical order. -/
def tripleProduct {α : Type*} (a b : Fin 3 → α) : Πₗ (_ : Fin 3), α × α := toLex (Pi.prod a b)

@[simp, category API, AMS 5]
theorem tripleProduct_const {α : Type*} (a : α) :
    tripleProduct (fun _ => a) (fun _ => a) = toLex (fun _ => (a, a)) := by
  simpa [tripleProduct] using funext fun i => by simp

@[simp, category API, AMS 5]
theorem tripleProduct_vecConst_const {α : Type*} (a : α) :
    tripleProduct ![a, a, a] ![a, a, a] = toLex ![(a, a), (a, a), (a, a)] := by
  simp [tripleProduct]
  ext i <;> fin_cases i <;> simp

/-- We define the product $\otimes$ of two sequences $(a_i, b_i, c_i)$ and
$(d_i, e_i, f_i)$ by the sequence $((a_i, d_j), (b_i, e_j), (c_i, f_j))$, where
the indices $(i, j)$ are arranged lexicographically, and the pairs are also
ordered lexicographically. -/
def sequenceProduct {α : Type*} (s t : List (Fin 3 → α)) : Lex (List (Πₗ (_ : Fin 3), α × α)) :=
  toLex (s.flatMap (fun a => List.map (tripleProduct a) t))

local infix:100 " ⊗₂ " => sequenceProduct

@[category test, AMS 5]
theorem sequenceProduct_example : [![1, 1, 1]] ⊗₂ [![1, 1, 1]] = toLex [toLex ![(1, 1), (1, 1), (1, 1)]] := by
  simp [sequenceProduct]

/-- Suppose that for some $n$ we have $F(n) = n ^ {\alpha}$. Then there are arbitrarily
large $m$ such that $F(m) \geq m^{\alpha}$. -/
@[category research solved, AMS 5]
theorem maximalLength_pow {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ e ≤ F m := by
  sorry

/-- $F(n) \leq n^{3/2}$. -/
@[category research open, AMS 5]
theorem maximalLength_le_strong (n : ℕ) : F n ≤ Real.sqrt n ^ 3 := by
  sorry

end Arxiv.«1609.08688»
