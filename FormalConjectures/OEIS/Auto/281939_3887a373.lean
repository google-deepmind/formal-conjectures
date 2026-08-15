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

open Int Nat Finset

/--
A281939: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z$ nonnegative integers and $w$ an integer,
and $x - y$ and $3z + w$ both squares.
-/
noncomputable def A281939 (n : ℕ) : ℕ :=
  let B : ℕ := n.sqrt
  let n_int : ℤ := n

  let S_nat : Finset ℕ := Finset.range (B + 1)
  let S_int : Finset ℤ := Finset.Icc (-(B : ℤ)) (B : ℤ)

  -- The set of all candidate quadruples (x, y, z, w) in a bounded box
  let Candidates : Finset (((ℕ × ℕ) × ℕ) × ℤ) :=
    (S_nat.product S_nat).product S_nat |>.product S_int

  (Candidates.filter fun p =>
    -- Unpack the nested tuple
    let x := p.fst.fst.fst;
    let y := p.fst.fst.snd;
    let z := p.fst.snd;
    let w := p.snd;

    let x_z : ℤ := x;
    let y_z : ℤ := y;
    let z_z : ℤ := z;

    -- Predicate for a non-negative integer k to be a perfect square in ℤ
    let is_perfect_square (k : ℤ) : Prop := k ≥ 0 ∧ Int.sqrt k * Int.sqrt k = k;

    -- Constraints
    -- 1. Sum of squares equals n
    x_z^2 + y_z^2 + z_z^2 + w^2 = n_int ∧
    -- 2. x - y is a square in ℤ
    is_perfect_square (x_z - y_z) ∧
    -- 3. 3z + w is a square in ℤ
    is_perfect_square (3 * z_z + w)
  ).card

open BigOperators

/--
Conjecture (i) in A281939: a(n) > 0 for all $n \ge 0$.
Every nonnegative integer $n$ can be written as $x^2 + y^2 + z^2 + w^2$ with
$x, y, z \in \mathbb{N}$, $w \in \mathbb{Z}$, and $x-y$ and $3z+w$ being perfect squares.
-/
theorem oeis_281939_conjecture_i : ∀ n : ℕ, A281939 n > 0 := by sorry
