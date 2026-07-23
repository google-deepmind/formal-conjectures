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

open Nat Finset BigOperators

open scoped Nat.Prime

/--
A238585: Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

theorem a_one : a 1 = 0 := by
  rfl

theorem a_two : a 2 = 0 := by
  sorry

theorem a_three : a 3 = 0 := by
  sorry

theorem a_four : a 4 = 1 := by
  sorry

/--
Conjecture: (i) a(n) > 0 unless n divides 6, and a(n) = 1 only for n = 4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44.
-/
theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) :=
by sorry
