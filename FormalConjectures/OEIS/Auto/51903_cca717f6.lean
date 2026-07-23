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
A051903: Maximum exponent in the prime factorization of $n$.
-/
def a (n : ℕ) : ℕ :=
  n.factorization.support.sup n.factorization

/--
A051903 (*) Are there composite numbers n > 4 such that n == a(n) (mod phi(n))?
This formalizes the conjecture that there are no such numbers.
Note: We use `¬ Nat.Prime n ∧ 4 < n` to formally express $n$ is a composite number greater than 4, as $4 < n$ implies $1 < n$.
-/
theorem oeis_51903_conjecture_0 :
  ¬ ∃ n, (¬ Nat.Prime n) ∧ 4 < n ∧ Nat.totient n ∣ (n - a n) := by
  sorry
