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

/-- The $x$-th triangular number. -/
def T (x : ℕ) : ℕ := x * (x + 1) / 2

/-- The number of primes not exceeding the $x$-th triangular number. -/
def pi_T (x : ℕ) : ℕ := Nat.primeCounting (T x)

/--
A262403: Number of ways to write $\pi(T(n)) = \pi(T(k)) + \pi(T(m))$ with $1 < k < m < n$,
where $T(x)$ is the triangular number $x(x+1)/2$, and $\pi(x)$ is the number of primes not exceeding x.
-/
def A262403 (n : ℕ) : ℕ :=
  let target_val := pi_T n
  -- The iteration ensures $1 < k$ and $k < m < n$
  (Icc 2 (n - 2)).sum fun k =>
    ((Icc (k + 1) (n - 1)).filter fun m =>
      target_val = pi_T k + pi_T m).card

/--
Conjecture (i): a(n) > 0 for all n > 4, and a(n) = 1 only for n = 5, 6, 7, 10, 12, 32, 38, 445, 727.
-/
theorem A262403_conjecture_i :
  (∀ n : ℕ, 4 < n → A262403 n > 0) ∧
  (∀ n : ℕ, 4 < n → (A262403 n = 1 ↔ n ∈ ({5, 6, 7, 10, 12, 32, 38, 445, 727} : Finset ℕ))) := by
  sorry

/--
Conjecture (ii) first assertion: All those numbers pi(T(n)) (n = 1,2,3,...) are pairwise distinct.
This is equivalent to the function x \mapsto pi(T(x))$ being injective.
-/
theorem A262403_conjecture_ii_distinctness :
  Function.Injective pi_T := by
  sorry
