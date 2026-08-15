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
open scoped Nat.Prime

/--
A263001: Number of ordered pairs $(k, m)$ with $k > 0$ and $m > 0$ such that
$n = \pi(k(k+1)) + \pi(m(m+1)/2)$, where $\pi(x)$ denotes the number of primes not exceeding $x$.
-/
noncomputable def A263001 (n : ℕ) : ℕ :=
  -- The set of solutions for a fixed n is finite. We count them by filtering over a large enough Finset.
  -- A bound of n+1 is sufficient for the definition, as k and m must be small relative to n.
  let bound : ℕ := n + 1
  let K_set : Finset ℕ := Icc 1 bound
  let M_set : Finset ℕ := Icc 1 bound

  (filter (fun p : ℕ × ℕ =>
    Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = n
  ) (Finset.product K_set M_set)).card


theorem a_one : A263001 1 = 1 := by
  -- This proof block from the prompt is incomplete/incorrectly written. We should remove the broken tactic calls.
  sorry

theorem a_two : A263001 2 = 0 := by
  sorry

theorem a_three : A263001 3 = 2 := by
  sorry

theorem a_four : A263001 4 = 1 := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 2, and a(n) = 1 only for n = 1, 4, 6.
-/
theorem oeis_a263001_conjecture :
  (∀ (n : ℕ), 2 < n → A263001 n > 0) ∧
  (∀ (n : ℕ), A263001 n = 1 ↔ n = 1 ∨ n = 4 ∨ n = 6) :=
by sorry
