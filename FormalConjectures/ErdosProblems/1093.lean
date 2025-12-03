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

/-!
# Erdős Problem 1093

*Reference:* [erdosproblems.com/1093](https://www.erdosproblems.com/1093)
-/

namespace Erdos1093

open Nat

/--
A number $n$ is $k$-smooth if all its prime factors are $\le k$.
-/
def IsKSmooth (k n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p ≤ k

/--
The deficiency is undefined if $\binom{n}{k}$ is divisible by a prime $p \le k$.
This predicate checks if the deficiency is *defined* (i.e., NO prime $p \le k$ divides it).
-/
def DeficiencyIsDefined (n k : ℕ) : Prop :=
  ∀ p, p.Prime → p ≤ k → ¬(p ∣ choose n k)

/--
If defined, the deficiency is the number of $0 \le i < k$ such that $n - i$ is $k$-smooth.
-/
noncomputable def deficiency (n k : ℕ) : ℕ :=
  ((List.range k).filter (fun i => IsKSmooth k (n - i))).length

/--
Conjecture:
1. Are there infinitely many binomial coefficients with deficiency 1?
2. Are there only finitely many with deficiency > 1?
-/
@[category research open, AMS 5]
theorem erdos_1093 :
  -- Part 1: Infinitely many pairs (n, k) with deficiency 1
  (∀ N, ∃ n > N, ∃ k, n > k ∧ DeficiencyIsDefined n k ∧ deficiency n k = 1) ∧
  -- Part 2: Finite number of pairs (n, k) with deficiency > 1
  (∃ S : Finset (ℕ × ℕ), ∀ n k, n > k → DeficiencyIsDefined n k → deficiency n k > 1 → (n, k) ∈ S) := by
  sorry

end Erdos1093
