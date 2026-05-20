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

open Nat Finset Set

/--
A275150: Number of ordered ways to write $n$ as $x^3 + 2y^2 + k z^2$, where $x,y,z$ are nonnegative integers, $k$ is $1$ or $5$, and $k = 1$ if $z = 0$.
The number of ways is the cardinality of the union of two disjoint sets of $(x, y, z)$ triples, categorized by the successful $k$ value.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the search space for (x, y, z). Since $x^3, 2y^2, 5z^2 \le n$, a safe upper bound is $n$.
  let R := range (n + 1)
  -- The search space is R x R x R, structured as ((x, y), z).
  let search_space := (R.product R).product R

  -- Set S1: Solutions to $n = x^3 + 2y^2 + z^2$ (corresponding to $k=1$).
  let S1 : Finset ((ℕ × ℕ) × ℕ) :=
    search_space.filter fun p =>
      let x := p.fst.fst; let y := p.fst.snd; let z := p.snd;
      x^3 + 2 * y^2 + z^2 = n

  -- Set S5: Solutions to $n = x^3 + 2y^2 + 5z^2$ with $z > 0$ (corresponding to $k=5$).
  let S5 : Finset ((ℕ × ℕ) × ℕ) :=
    search_space.filter fun p =>
      let x := p.fst.fst; let y := p.fst.snd; let z := p.snd;
      x^3 + 2 * y^2 + 5 * z^2 = n ∧ z ≠ 0

  -- The total number of ways is |S1| + |S5|.
  S1.card + S5.card


theorem a_zero : a 0 = 1 := by
  sorry

theorem a_one : a 1 = 2 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 2 := by
  sorry


/--
Conjecture 2: For any positive integers a, b, c and integers i, j, k greater than one, there are infinitely many positive integers not in the set $\{a \cdot x^i + b \cdot y^j + c \cdot z^k: x,y,z = 0,1,2,...\}$.
This is a representation problem about sums of three terms with fixed positive coefficients and powers greater than one.
-/
theorem oeis_a275150_conjecture_2_sun :
  ∀ (a b c i j k : ℕ),
    -- a, b, c are positive integers
    0 < a → 0 < b → 0 < c →
    -- i, j, k are integers greater than one
    1 < i → 1 < j → 1 < k →
  (let S : Set ℕ := {n | ∃ x y z : ℕ, n = a * x^i + b * y^j + c * z^k}
   -- The set of positive integers not in S is infinite
   Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S}) := by sorry
