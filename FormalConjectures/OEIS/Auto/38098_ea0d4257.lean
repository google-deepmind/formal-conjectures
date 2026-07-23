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
A038098: Number of primes $< n^3$.
This is the cardinality of the set of prime numbers less than $n^3$.
Formally, this is $| \{p \in \mathbb{P} \mid p < n^3 \}|$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (range (n ^ 3))).card


theorem a_one : a 1 = 0 := by
  exact rfl

theorem a_two : a 2 = 4 := by
  sorry

theorem a_three : a 3 = 9 := by
  sorry

theorem a_four : a 4 = 18 := by
  sorry

/--
Conjecture: (i) For any integer k > 2 the sequence pi(n^k)/n^k (n = 2,3,...) is strictly decreasing, where pi(x) denotes the number of primes not exceeding x.

Note: pi(x) is formalized as Nat.primeCounting x.
-/
theorem oeis_38098_conjecture_0 :
  ∀ k : ℕ, 2 < k →
  ∀ n : ℕ, 2 ≤ n →
  (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) > (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) :=
by sorry
