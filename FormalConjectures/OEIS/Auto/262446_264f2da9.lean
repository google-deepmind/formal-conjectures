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
The auxiliary sequence $A262439$: $a(n) = \pi(\frac{n(n+1)}{2} + 1)$, where $\pi(x)$ is the prime-counting function.
-/
def A262439 (n : ℕ) : ℕ :=
  primeCounting (n * (n + 1) / 2 + 1)

/--
A262446: Number of ways to write $A262439(n) = A262439(k) + A262439(m)$ with $0 < k < m < n$.
-/
def A262446 (n : ℕ) : ℕ :=
  -- We iterate over $k$ such that $1 \le k < n$.
  (Ico 1 n).sum fun k =>
    -- We iterate over $m$ such that $k + 1 \le m < n$.
    (Ico (k + 1) n).sum fun m =>
      if A262439 n = A262439 k + A262439 m then 1 else 0

/-- The set of $n$ for which the conjecture claims A262446(n) = 1. -/
def A262446_unique_n_set : Finset ℕ :=
  {4, 6, 11, 21, 54, 253, 325}

/--
%C A262446 I have verified the conjecture for n up to 10^5. - _Zhi-Wei Sun_, Sep 27 2015
The mathematical statement verified up to $10^5$ is that the full conjecture holds for $3 < n \le 100000$.
-/
theorem A262446_conjecture_verified_upto_10e5 :
  ∀ n : ℕ, 3 < n ∧ n ≤ 100000 → A262446 n > 0 ∧ (A262446 n = 1 ↔ n ∈ A262446_unique_n_set) := by
  sorry
