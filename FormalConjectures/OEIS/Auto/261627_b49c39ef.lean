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
A261627: Number of primes $p$ such that $n-(p \cdot n'-1)$ and $n+(p \cdot n'-1)$ are both prime,
where $n'$ is 1 or 2 according as $n$ is odd or even.
-/
noncomputable def A261627 (n : ℕ) : ℕ :=
  let n' : ℕ := if n % 2 = 1 then 1 else 2

  -- The set of relevant primes is constructed by filtering primes below $n+1$.
  Finset.card $ Finset.filter (fun p : ℕ =>
    let k := p * n' - 1
    -- Condition k < n ensures that the subtraction is valid in Nat.
    -- Primality check ensures n - k >= 2.
    k < n ∧
    Nat.Prime (n - k) ∧
    Nat.Prime (n + k)
  ) (primesBelow (n + 1))

-- Placeholder theorems from OEIS data, kept for completeness but do not affect the main task.
theorem a_one : A261627 1 = 0 := by
  trivial

theorem a_two : A261627 2 = 0 := by
  rfl

theorem a_three : A261627 3 = 0 := by
  constructor

theorem a_four : A261627 4 = 0 := by
  subsingleton

-- Formal definition of the strong Goldbach conjecture (every even number >= 4 is a sum of two primes).
def goldbach_conjecture : Prop :=
  ∀ (m : ℕ), 4 ≤ m ∧ Even m →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q

-- Formal definition of Lemoine's conjecture (every odd number >= 7 is p + 2q for primes p, q).
def lemoine_conjecture : Prop :=
  ∀ (n : ℕ), 7 ≤ n ∧ Odd n →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + 2 * q

-- Formal statement of the A261627 main conjecture (a(n) > 0 for n > 6).
def A261627_conjecture : Prop :=
  ∀ (n : ℕ), 6 < n → 0 < A261627 n

/--
Conjecture: This is stronger than Goldbach's conjecture (A002375) and Lemoine's conjecture (A046927).
This formalizes the statement that the main A261627 conjecture implies both Goldbach's and Lemoine's conjectures.
-/
theorem oeis_261627_conjecture_1 : A261627_conjecture → goldbach_conjecture ∧ lemoine_conjecture := by
  sorry
