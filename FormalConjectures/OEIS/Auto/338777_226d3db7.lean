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

open Nat Finset

/--
A338777: $a(n) = \prod_{k \in \text{GB}(2n)} k$, where $\text{GB}(m)$ is the set of primes $p$
such that $\sqrt{m} < p \le m/2$ and no prime $q \le \sqrt{m}$ divides $p(p - m)$.
The condition $q \nmid p(p-m)$ is equivalent to $p \not\equiv m \pmod q$ for $p \in \text{GB}(m)$.
-/
def A338777 (n : ℕ) : ℕ :=
  let m := 2 * n
  -- The product over an empty set is 1, which handles a(0), a(1), a(2) correctly.
  if m = 0 then 1 else

  let r := Nat.sqrt m
  -- The set of primes q that are candidates for dividing p(p-m).
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime

  -- A number p is Goldbach-associated with m if it satisfies the criteria.
  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧
    r < p ∧
    p ≤ m / 2 ∧
    (∀ q ∈ small_primes, p % q ≠ m % q)

  -- GB(m) is the set of primes p up to m/2 that satisfy the condition.
  let GB_2n : Finset ℕ :=
    (Finset.range (m / 2 + 1)).filter is_gb_associated

  GB_2n.prod id

-- An auxiliary definition for the Goldbach-associated set GB(m) for use in the conjecture.
def GB_set (m : ℕ) : Finset ℕ :=
  if m = 0 then ∅ else
  let r := Nat.sqrt m
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime

  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧
    r < p ∧
    p ≤ m / 2 ∧
    (∀ q ∈ small_primes, p % q ≠ m % q)

  (Finset.range (m / 2 + 1)).filter is_gb_associated

/-- The Goldbach conjecture states that every even integer greater than 2 is the sum of two primes. -/
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ p1 p2 : ℕ, Nat.Prime p1 ∧ Nat.Prime p2 ∧ 2 * n = p1 + p2

/-- Simple check of initial values. -/
theorem a_zero : A338777 0 = 1 := by sorry
theorem a_one : A338777 1 = 1 := by sorry
theorem a_two : A338777 2 = 1 := by sorry
theorem a_three : A338777 3 = 3 := by sorry

/-- oeis_338777_conjecture_0: If a(n) != 1 for n >= 3 then Goldbach's conjecture is true.
The underlying claim is that for any such $n$, $m = \max(\text{GB}(2n))$ exists and $(2n - m, m)$
is a Goldbach partition of $2n$. -/
theorem oeis_338777_conjecture_0 :
  -- The claim that the sequence property implies Goldbach's conjecture globally.
  ( (∀ k : ℕ, 3 ≤ k → A338777 k ≠ 1) → goldbach_conjecture ) ∧
  -- The local constructive claim for each n: A(n) != 1 implies a specific Goldbach partition.
  (∀ n : ℕ, 3 ≤ n →
    A338777 n ≠ 1 →
      let m2n := 2 * n
      let GB_2n := GB_set m2n
      -- A(n) != 1 implies GB(2n) is Nonempty, thus a maximum exists.
      GB_2n.Nonempty ∧
      -- Existential quantification for the maximum element m in GB(2n)
      ∃ m : ℕ, m ∈ GB_2n ∧ (∀ k ∈ GB_2n, k ≤ m) ∧
      -- Since m is a prime in GB_2n, the conjecture is that the complement is also prime.
      Nat.Prime (m2n - m)
      ) := by
  sorry
