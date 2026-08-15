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

open Nat Set

/--
A084046: Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such number exists.
I.e., smallest prime of the form $k^n - n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- S_n is the set of primes p such that p + n is an n-th power, i.e., p = k^n - n.
  let S_n : Set ℕ := { p | Nat.Prime p ∧ ∃ k : ℕ, k ^ n = p + n }
  -- sInf S_n returns the smallest element of S_n. For Nat, sInf ∅ = 0, fitting the problem statement.
  sInf S_n

/-- Conjecture: if a(k) = 0 then k is an even square. -/
theorem a084046_conjecture_0 :
  ∀ k : ℕ, a k = 0 → ∃ m : ℕ, k = (2 * m) ^ 2 :=
by sorry
