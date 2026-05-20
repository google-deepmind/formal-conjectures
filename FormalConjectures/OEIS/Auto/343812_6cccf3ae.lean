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
A343812: $a(n) = \sum_{i \le n} (A007504(n) \bmod \mathrm{prime}(i))$.
$A007504(n)$ is the sum of the first $n$ primes, and $\mathrm{prime}(i)$ is the $i$-th prime.
The index $i$ runs from $1$ to $n$, which corresponds to $k=0$ to $n-1$ in 0-indexing.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- A007504(n), the sum of the first n primes.
  let S_n : ℕ := (range n).sum (fun k => Nat.nth Nat.Prime k)

  -- The result is the sum of S_n modulo the first n primes.
  (range n).sum (fun i => S_n % (Nat.nth Nat.Prime i))


theorem a_one : a 1 = 0 := by
  delta a
  simp_all

theorem a_two : a 2 = 3 := by
  delta a
  norm_num [Finset.sum]

theorem a_three : a 3 = 1 := by
  delta a
  norm_num[Finset.sum]

theorem a_four : a 4 = 8 := by
  delta a
  norm_num [Finset.sum]

/-- A343812 Does any term occur more than once? (Conjectured to be "no" for $n \ge 1$). -/
theorem A343812_conjecture (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : a m = a n → m = n := by
  sorry
