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

open Nat Int Finset

/--
A282091: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + y - z$ a cube of an integer,
where $x,y,z,w$ are nonnegative integers with $x \ge y \le z$ and $x \equiv y \pmod 2$.
-/

-- Helper predicate for the core number theory constraint
def is_perfect_cube (m : ℤ) : Prop := ∃ k : ℤ, m = k ^ 3

-- We assert this is decidable using classical logic, as it is true constructively.
noncomputable instance decidable_is_perfect_cube (m : ℤ) : Decidable (is_perfect_cube m) :=
  Classical.dec _

noncomputable def A282091 (n : ℕ) : ℕ :=
  let B := n.sqrt + 1
  let R := Finset.range B

  let is_square (m : ℕ) : Prop := m.sqrt * m.sqrt = m

  -- Search space for (x, y, z) in N^3
  let search_space := R.product R |>.product R

  search_space.filter (fun p : (ℕ × ℕ) × ℕ =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd

    let sum_xyz_sq := x^2 + y^2 + z^2
    let w_sq := n - sum_xyz_sq

    -- 1. Ensure $w^2 \ge 0$ (i.e., sum_xyz_sq ≤ n)
    sum_xyz_sq ≤ n ∧
    -- 2. Ensure $w^2$ is a perfect square, implicitly defining $w \in \mathbb{N}$
    is_square w_sq ∧

    -- 3. Order constraints: $x \ge y \le z$
    x ≥ y ∧ y ≤ z ∧

    -- 4. Parity constraint: $x \equiv y \pmod 2$
    (x % 2 = y % 2) ∧

    -- 5. Cube constraint on $x + y - z$
    is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ))
  )
  |>.card


-- Proof stubs for context, as provided in the prompt
theorem a_zero : A282091 0 = 1 := by sorry
theorem a_one : A282091 1 = 2 := by sorry
theorem a_two : A282091 2 = 1 := by sorry
theorem a_three : A282091 3 = 1 := by sorry

/--
  Conjecture (i) from OEIS A282091:
  a(n) > 0 for all n = 0,1,2,....
  Also, any nonnegative integer n can be written as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers
  and $x \le y \le z$ such that $x + y - z$ is a cube of an integer.
-/
theorem oeis_282091_conjecture_0 :
  -- Part 1: a(n) > 0
  (∀ n : ℕ, A282091 n > 0) ∧
  -- Part 2: Existence with different constraints (x ≤ y ≤ z)
  (∀ n : ℕ, ∃ x y z w : ℕ,
      n = x^2 + y^2 + z^2 + w^2 ∧
      x ≤ y ∧ y ≤ z ∧
      is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ))) :=
by sorry
