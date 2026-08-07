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
A263206: Number of primes $p$ with $\text{prime}(p) \in (n^2, (n+2)^2)$, where $p$ is a prime index.
The term $\text{prime}(p)$ here refers to the $p$-th prime number.
Let $\pi(x) = \text{Nat.primeCounting } x$ be the prime counting function.
The indices $i$ such that $\text{prime}(i) \in (n^2, (n+2)^2)$ start at $L = \pi(n^2) + 1$
and end at $R = \pi((n+2)^2 - 1)$.
The sequence value $a(n)$ is the number of primes $p$ such that $L \le p \le R$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The least index $i$ (1-based) such that $\text{prime}(i) > n^2$ is $\pi(n^2) + 1$.
  let L : ℕ := (n^2).primeCounting + 1
  -- The greatest index $i$ (1-based) such that $\text{prime}(i) < (n+2)^2$ is $\pi((n+2)^2 - 1)$.
  let R : ℕ := ((n + 2)^2 - 1).primeCounting
  -- The number of primes $p$ such that $L \le p \le R$ is $\pi(R) - \pi(L-1)$.
  R.primeCounting - (L - 1).primeCounting


theorem a_one : a 1 = 2 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 2 := by
  sorry

theorem a_four : a 4 = 2 := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 0. In other words, for each n = 1,2,3,... the interval (n^2, (n+2)^2) contains a prime with prime subscript.
-/
theorem oeis_a263206_conjecture_0 (n : ℕ) : 0 < n → a n > 0 := by
  sorry
