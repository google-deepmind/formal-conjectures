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

open Nat Finset Set BigOperators

/--
$P_k$ is the product of the first $k$ primes.
-/
noncomputable def prod_first_k_primes (k : ℕ) : ℕ :=
  (range k).prod (fun i => Nat.nth Nat.Prime i)

/--
A210186: $a(n) = \text{least integer } m>1 \text{ such that } m \text{ divides none of } P_i + P_j$
with $0<i<j \le n$ where $P_k$ is the product of the first $k$ primes.
-/
noncomputable def A210186 (n : ℕ) : ℕ :=
  sInf { m : ℕ |
    1 < m ∧
    ∀ i j : ℕ,
      (1 ≤ i ∧ i < j ∧ j ≤ n) →
      ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }


theorem a_one : A210186 1 = 2 := by
  sorry

theorem a_two : A210186 2 = 3 := by
  sorry

theorem a_three : A210186 3 = 5 := by
  sorry

theorem a_four : A210186 4 = 7 := by
  sorry


/--
A210186 Conjecture: all the terms are primes and a(n) < n^2 for all n > 1.
- $\forall n : \mathbb{N}, \text{Prime } (A210186(n))$
- $\forall n : \mathbb{N}, n > 1 \implies A210186(n) < n^2$
-/
theorem oeis_210186_conjecture :
  (∀ n : ℕ, Nat.Prime (A210186 n)) ∧ (∀ n : ℕ, 1 < n → A210186 n < n^2) := by
  sorry
