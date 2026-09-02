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

  -- We check primes $p \le n$.
  let candidate_primes : Finset ℕ := Finset.filter Nat.Prime (Finset.range (n + 1))

  Finset.card $ Finset.filter (fun p : ℕ =>
    Nat.Prime p ∧ -- p must be prime
    let k : ℕ := p * n' - 1 -- k >= 1 since p >= 2 and n' >= 1
    k < n ∧ -- Condition k < n ensures that the subtraction (n - k) is valid in Nat.
    Nat.Prime (n - k) ∧
    Nat.Prime (n + k)
  ) candidate_primes

/-- The set of exceptional $n$ values for which $A261627(n) = 1$. -/
def A261627_singletons : Finset ℕ :=
  ([5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142] : List ℕ).toFinset

/--
OEIS A261627 Conjecture: a(n) > 0 for all n > 6, and a(n) = 1 only for
n = 5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142.
-/
theorem oeis_261627_conjecture_0 (n : ℕ) :
  (n > 6 → A261627 n > 0) ∧
  (A261627 n = 1 ↔ n ∈ A261627_singletons) :=
by sorry
