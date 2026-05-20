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

open Nat Set Finset

/--
A290012: $a(n)$ is the smallest prime number $p$ satisfying
$$p^2 \ge \sum_{1 \le k \le n} \mathrm{prime}(k)^2$$
where $\mathrm{prime}(k)$ is the $k$-th prime number.
-/
noncomputable def A290012 (n : ℕ) : ℕ :=
  let S_n : ℕ := (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)
  -- sInf finds the smallest element of the set of primes p that satisfy the condition.
  sInf { p : ℕ | p.Prime ∧ S_n ≤ p ^ 2 }

/-- Conjecture: The only twin prime pair in the sequence is (5, 7).
This means the property A290012(n+1) = A290012(n) + 2 holds if and only if n = 2. -/
theorem oeis_a290012_conjecture_unique_twin_prime :
  ∀ n : ℕ, 1 ≤ n → (A290012 (n + 1) = A290012 n + 2 ↔ n = 2) :=
by sorry
