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

open Finset Nat

/--
A060957: Number of different products (including the empty product) of any subset of $\{1, 2, 3, \dots, n\}$.
-/
def A060957 (n : ℕ) : ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id) |>.card

-- Convenience definition for the set of products
private def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

/--
Conjecture: Let p <= n be prime. If m and p^a*m are two such products, then so is p^k*m for all 0 < k < a.
-/
theorem oeis_60957_conjecture_0 (n : ℕ) :
    ∀ p, Nat.Prime p → p ≤ n →
    ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
    ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by sorry
