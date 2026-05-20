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
A335624: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 3y + 4z$ a square,
where $x, y, z, w$ are nonnegative integers.
-/
def A335624 (n : ℕ) : ℕ :=
  -- The variables x, y, z, w are bounded by sqrt(n), since they are non-negative.
  let B : ℕ := Nat.sqrt n + 1
  let R := range B

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      -- The term x + 3*y + 4*z must be a perfect square.
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

theorem a_zero : A335624 0 = 1 := by
  -- The search space for x, y, z, w is range 1, so x=y=z=w=0.
  -- 0^2 + 0^2 + 0^2 + 0^2 = 0.
  -- 0 + 3*0 + 4*0 = 0, which is 0^2.
  -- Count is 1.
  sorry

theorem a_one : A335624 1 = 3 := by
  -- (1,0,0,0), (0,1,0,0), (0,0,1,0) all satisfy sum=1, but we need x+3y+4z to be a square.
  -- (1,0,0,0): 1+0+0+0=1. x+3y+4z = 1. 1 is 1^2. (1,0,0,0) is a solution.
  -- (0,1,0,0): 0+1+0+0=1. x+3y+4z = 3. 3 is not a square.
  -- (0,0,1,0): 0+0+1+0=1. x+3y+4z = 4. 4 is 2^2. (0,0,1,0) is a solution.
  -- ... and permutations of w give solutions, the count should be 3: (1,0,0,0), (0,0,1,0) and (0,0,0,1) where w=1/w=0/w=0
  -- No, the variables are ordered: x,y,z,w.
  -- The solutions for n=1 are:
  -- (1,0,0,0): 1^2+...=1. x+3y+4z=1=1^2.
  -- (0,0,0,1): ...+1^2=1. x+3y+4z=0=0^2.
  -- (0,0,0,1): Wait, w is the fourth variable.
  -- x^2+y^2+z^2+w^2 = 1. Solutions are permutations of (1,0,0,0).
  -- 1. (1,0,0,0): 1+0+0=1=1^2.
  -- 2. (0,1,0,0): 0+3+0=3. Not square.
  -- 3. (0,0,1,0): 0+0+4=4=2^2.
  -- 4. (0,0,0,1): 0+0+0=0=0^2.
  -- Count is 3. (1,0,0,0), (0,0,1,0), (0,0,0,1). This matches A335624(1)=3.
  sorry

theorem a_two : A335624 2 = 3 := by
  sorry

theorem a_three : A335624 3 = 1 := by
  sorry

/--
Conjecture: a(n) = 0 if and only if n has the form $2^{4k+3} \cdot m$ (k >= 0 and m = 1, 3, 5, 43).
This is the main part of the OEIS conjecture.
-/
theorem A335624_conjecture_zero_iff (n : ℕ) :
  A335624 n = 0 ↔
    ∃ (k : ℕ) (m : ℕ),
      m ∈ ({1, 3, 5, 43} : Set ℕ) ∧
      n = 2 ^ (4 * k + 3) * m :=
by sorry
