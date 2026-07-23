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

open Nat

/--
A259667: Catalan numbers mod 6.
$$a(n) = C_n \bmod 6$$
where $C_n = \frac{1}{n+1} \binom{2n}{n}$ is the $n$-th Catalan number (A000108).
-/
def A259667 (n : ℕ) : ℕ := ((2 * n).choose n / (n + 1)) % 6

/--
It is conjectured that the only k which yield a(2^k-1) = 1 are k = 0, 1 and 5.
Are there other k than 2 and 8 that yield a(2^k-1) = 5?
Otherwise said, is a(2^k-1) = 3 for all k > 8.
-/
theorem oeis_259667_conjecture_0 :
    (∀ k : ℕ, A259667 (2^k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5) ∧
    (∀ k : ℕ, A259667 (2^k - 1) = 5 ↔ k = 2 ∨ k = 8) ∧
    (∀ k : ℕ, k > 8 → A259667 (2^k - 1) = 3) := by
  sorry
