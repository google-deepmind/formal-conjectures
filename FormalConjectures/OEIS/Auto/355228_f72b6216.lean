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

open Finset Nat Set

/--
A355228: $a(n)$ is the smallest integer $m$ such that there exist $n$ of its distinct divisors $(d_1, d_2, \dots, d_n)$ with the property that $m = d_1 + d_2 + \dots + d_n = \operatorname{lcm}(d_1, d_2, \dots, d_n)$, or 0 if no such number $m$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidates $m$ for the given $n$.
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      -- There exists a set D of n distinct elements
      ∃ D : Finset ℕ,
        -- D must be a subset of m's positive divisors.
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        -- The sum of elements in D must equal m.
        D.sum id = m ∧
        -- The LCM of elements in D must equal m.
        D.lcm id = m }

  -- sInf of a set of natural numbers returns the minimum element.
  -- Nat.sInf of the empty set is 0, correctly handling the non-existence case a(2)=0.
  sInf candidates


theorem a_one : a 1 = 1 := by
  sorry -- Proof is trivial: {1} is a set of 1 divisor of 1, sum=1, lcm=1.

theorem a_two : a 2 = 0 := by
  -- Proof requires showing that the candidate set is empty, which relies on
  -- the fact that if m = d₁ + d₂ = lcm(d₁, d₂), then d₁ = d₂, contradicting distinctness.
  sorry

theorem a_three : a 3 = 6 := by
  -- Example: m=6, D={1, 2, 3}. Sum = 6, lcm(1, 2, 3) = 6.
  sorry

theorem a_four : a 4 = 18 := by
  -- Example: m=18, D={1, 2, 6, 9}. Sum = 18, lcm(1, 2, 6, 9) = 18.
  sorry

-- A081512: Smallest number $m$ such that $m$ is the sum of $n$ distinct divisors $d_1, \dots, d_n$ of $m$.
noncomputable def a081512 (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m }
  sInf candidates

/--
A355228 a(n) >= A081512(n) because in A081512, it is not required that m = lcm(d_1, d_2, ..., d_n).
Currently, the strict inequality happens for n = 4 and n = 5; are there other such cases?

This conjecture states that the set of natural numbers $n$ for which the strict inequality $a(n) > a_081512(n)$ holds is exactly $\{4, 5\}$.
-/
theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  sorry
