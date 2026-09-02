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
A279056: Number of ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ with $w$ a positive integer
and $x,y,z$ nonnegative integers such that $x^3 + 4yz(y-z)$ is a square.
-/
def A279056 (n : ℕ) : ℕ :=
  if n = 0 then 0 else

  -- The bound is $\lfloor\sqrt{n}\rfloor + 1$, which is sufficient to contain all solutions.
  let B : ℕ := n.sqrt + 1
  let R : Finset ℕ := range B

  -- The search space has type ℕ × ℕ × ℕ × ℕ, representing $(w, x, y, z)$.
  let S := ((R.product R).product R).product R

  Finset.card $ S.filter fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd

    -- The cubic expression condition, evaluated in ℤ.
    let square_cond : Prop :=
      let val : ℤ := (x : ℤ)^3 + 4 * (y : ℤ) * (z : ℤ) * ((y : ℤ) - (z : ℤ))
      IsSquare val

    -- w > 0 and the sum of squares equals n.
    w > 0 ∧
    w^2 + x^2 + y^2 + z^2 = n ∧
    square_cond

-- Placeholder theorems from the original prompt (modified to avoid immediate failure by using sorry)
theorem a_one : A279056 1 = 1 := by sorry
theorem a_two : A279056 2 = 3 := by sorry
theorem a_three : A279056 3 = 3 := by sorry
theorem a_four : A279056 4 = 2 := by sorry


/--
The formalized conjecture from OEIS A279056: (i) a(n) > 0 for all n > 0.
-/
lemma A279056_conjecture_i (n : ℕ) (hn : n > 0) : 0 < A279056 n := by sorry

/--
Define the count for part (ii) of the conjecture:
Number of ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ with $w$ a positive integer
and $x,y,z$ nonnegative integers such that $x^3 + 8yz(2y-z)$ is a square.
-/
def B_A279056 (n : ℕ) : ℕ :=
  if n = 0 then 0 else

  let B : ℕ := n.sqrt + 1
  let R : Finset ℕ := range B
  let S := ((R.product R).product R).product R

  Finset.card $ S.filter fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd

    -- The cubic expression condition for part (ii), evaluated in ℤ.
    -- x^3 + 8*y*z*(2*y - z)
    let square_cond : Prop :=
      let val : ℤ := (x : ℤ)^3 + 8 * (y : ℤ) * (z : ℤ) * (2 * (y : ℤ) - (z : ℤ))
      IsSquare val

    -- w > 0 and the sum of squares equals n.
    w > 0 ∧
    w^2 + x^2 + y^2 + z^2 = n ∧
    square_cond

/--
Conjecture (ii) from A279056: Any positive integer n can be written as
$w^2 + x^2 + y^2 + z^2$ with $w$ a positive integer and $x,y,z$ nonnegative integers
such that $x^3 + 8yz(2y-z)$ is a square.
This is equivalent to $B\_A279056(n) > 0$ for all $n > 0$.
-/
theorem A279056_conjecture_ii (n : ℕ) (hn : n > 0) : 0 < B_A279056 n := by sorry

/--
Claim from A279056: We have verified a(n) > 0 and part (ii) of the conjecture for n up to 3*10^5.
Note: This claim summarizes two conjectures verified computationally up to a bound.
-/
theorem A279056_verified_up_to_300000 (n : ℕ) (hn : n > 0) (hn_bound : n ≤ 300000) :
  0 < A279056 n ∧ 0 < B_A279056 n := by sorry
