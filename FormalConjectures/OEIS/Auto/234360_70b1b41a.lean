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
A234360: $a(n) = \left|\left\{0 < k < n: (k+1)^{\phi(n-k)} + k \text{ is prime}\right\}\right|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (filter (fun k => Nat.Prime ((k + 1) ^ (Nat.totient (n - k)) + k)) (Ico 1 n)).card

/-- Conjecture: (i) a(n) > 0 for all n > 1. Also, for any n > 5 there is a positive integer k < n with (k+1)^{phi(n-k)/2} - k prime. -/
theorem oeis_234360_conjecture_0 :
  (∀ n, 1 < n → 0 < a n) ∧
  (∀ n, 5 < n → ∃ k, 0 < k ∧ k < n ∧ Nat.Prime ((k + 1) ^ (Nat.totient (n - k) / 2) - k)) :=
by sorry
