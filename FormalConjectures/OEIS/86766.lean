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
# Smallest $r$ such that (concatenation of $n$, $r$ times) $\cdot 10 + 1$ is prime

$a(n)$ is the smallest $r$ where (concatenation of $n$, $r$ times with itself) $\cdot 10 + 1$
is a prime, or $0$ if no such number exists.
The number resulting from concatenating $n$, $r$ times, is
$n \cdot \sum_{i=0}^{r-1} (10^d)^i$, where $d$ is the number of digits of $n$.

*References:*
- [A086766](https://oeis.org/A086766)-/

namespace OeisA86766

/-- Sequence $a(n)$ is the smallest $r > 0$ such that the concatenation of $n$, $r$ times
with itself, multiplied by $10$ plus $1$, is prime, or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ
    let repCatVal (r : ℕ) : ℕ := n * ∑ i ∈ Finset.range r, M ^ i
    let primeCandidate (r : ℕ) : ℕ := repCatVal r * 10 + 1
    sInf {r : ℕ | 0 < r ∧ (primeCandidate r).Prime}

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((1 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  1).length) ^ i) * 10 + 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_setOf_eq]
      refine ⟨by omega, ?_⟩
      have : (Nat.digits 10 1).length = 1 := by decide +native
      rw [this]
      norm_num
    · intro r hr
      simp only [Set.mem_setOf_eq] at hr
      exact hr.1
  have ha1 : a 1 = sInf {r : ℕ | 0 < r ∧ ((1 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  1).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha1, h_least.csInf_eq]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have h_digits : (Nat.digits 10 2).length = 1 := by decide +native
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((2 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  2).length) ^ i) * 10 + 1).Prime} 3 := by
    constructor
    · simp only [Set.mem_setOf_eq]
      refine ⟨by omega, ?_⟩
      rw [h_digits]
      norm_num
    · intro r hr
      simp only [Set.mem_setOf_eq] at hr
      by_contra! h
      have hr_pos := hr.1
      interval_cases r
      · have hr2 := hr.2
        rw [h_digits] at hr2
        revert hr2
        norm_num
      · have hr2 := hr.2
        rw [h_digits] at hr2
        revert hr2
        norm_num
  have ha2 : a 2 = sInf {r : ℕ | 0 < r ∧ ((2 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  2).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha2, h_least.csInf_eq]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((3 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  3).length) ^ i) * 10 + 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_setOf_eq]
      refine ⟨by omega, ?_⟩
      have : (Nat.digits 10 3).length = 1 := by decide +native
      rw [this]
      norm_num
    · intro r hr
      simp only [Set.mem_setOf_eq] at hr
      exact hr.1
  have ha3 : a 3 = sInf {r : ℕ | 0 < r ∧ ((3 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  3).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha3, h_least.csInf_eq]

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((4 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  4).length) ^ i) * 10 + 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_setOf_eq]
      refine ⟨by omega, ?_⟩
      have : (Nat.digits 10 4).length = 1 := by decide +native
      rw [this]
      norm_num
    · intro r hr
      simp only [Set.mem_setOf_eq] at hr
      exact hr.1
  have ha4 : a 4 = sInf {r : ℕ | 0 < r ∧ ((4 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  4).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha4, h_least.csInf_eq]

open scoped Classical in
/--
What is the smallest integer $m > 1$ such that $a(10^m)$ is nonzero?
- _Farideh Firoozbakht_, Jan 07 2015
-/
@[category research open, AMS 11]
theorem conjecture1 :
    answer(sorry) =
      if h : ∃ m, 1 < m ∧ a (10 ^ m) ≠ 0 then
        some (sInf {m | 1 < m ∧ a (10 ^ m) ≠ 0})
      else
        none := by
  sorry


/--
Conjecture: If $n$ is not of the form $10^m$ then $a(n)$ is nonzero.
- _Farideh Firoozbakht_, Jan 07 2015
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 0 < n) (h : ∀ m : ℕ, n ≠ 10 ^ m) : a n ≠ 0 := by
  sorry

open scoped Classical in
/--
What is the smallest odd prime $p$ such that $(10^{p^2}-1)/(10^p-1)$ is a prime number
(and $a(10^{p-1})$ could be nonzero)?
- _Farideh Firoozbakht_, Jan 07 2015
-/
@[category research open, AMS 11]
theorem conjecture3 :
    answer(sorry) =
      if h : ∃ p, p.Prime ∧ 2 < p ∧ ((10 ^ (p ^ 2) - 1) / (10 ^ p - 1)).Prime then
        some (sInf {p | p.Prime ∧ 2 < p ∧ ((10 ^ (p ^ 2) - 1) / (10 ^ p - 1)).Prime})
      else
        none := by
  sorry

end OeisA86766

