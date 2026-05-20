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
A005258(n): The Apéry numbers $B(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}$.
-/
def A005258 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (n.choose k) ^ 2 * ((n + k).choose k)

/--
A357506: $a(n) = A005258(n)^3 \cdot A005258(n-1)$.
The sequence is indexed starting from $n=1$.
-/
def a (n : ℕ) : ℕ :=
  (A005258 n) ^ 3 * (A005258 (n - 1))


theorem a_one : a 1 = 27 := by
  sorry

theorem a_two : a 2 = 20577 := by
  sorry

theorem a_three : a 3 = 60353937 := by
  sorry

theorem a_four : a 4 = 287798988897 := by
  sorry

/--
The stronger congruence $a(p) \equiv 27 \pmod{p^5}$ holds for all primes $p \ge 3$.
-/
theorem oeis_a357506_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → p ≥ 3 → a p ≡ 27 [MOD (p ^ 5)] := by
  sorry
