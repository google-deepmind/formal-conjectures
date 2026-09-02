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
A290472: Number of ways to write $6n+1$ as $x^2 + 3y^2 + 7z^2$, where $x$ is a positive integer, and $y$ and $z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  -- A search bound R is sufficient since x, y, z are at most sqrt(N).
  let R : ℕ := Nat.sqrt N + 1

  let X := Finset.range R
  let Y := Finset.range R
  let Z := Finset.range R

  -- The search space is the Cartesian product of the three ranges.
  let search_space := X.product (Y.product Z)

  Finset.card $ Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd

    -- Constraint 1: x must be positive (x \in \mathbb{Z}_{>0})
    x > 0 ∧
    -- Constraint 2: The equation must hold
    x * x + 3 * y * y + 7 * z * z = N
  ) search_space

theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 1 := by sorry
theorem a_two : a 2 = 1 := by sorry
theorem a_three : a 3 = 2 := by sorry

/--
In support of the first conjecture, a(n) > 1 for $286 < n \le 10^7$.
-/
theorem oeis_290472_conjecture_3 :
  ∀ n : ℕ, 286 < n ∧ n ≤ 10000000 → a n > 1 :=
by sorry
