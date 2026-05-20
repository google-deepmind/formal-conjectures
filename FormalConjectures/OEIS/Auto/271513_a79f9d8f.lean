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

open Nat Finset BigOperators Int

/--
A271513: Number of ordered ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ with $3x^2 + 4y^2 + 9z^2$ a square,
where $w, x, y$ and $z$ are nonnegative integers.
-/
def A271513 (n : ℕ) : ℕ :=
  let is_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m
  let B := Nat.sqrt n
  let R := Finset.range (B + 1)

  Finset.sum R fun w =>
    Finset.sum R fun x =>
      Finset.sum R fun y =>
        Finset.sum R fun z =>
          if w^2 + x^2 + y^2 + z^2 = n ∧ is_square (3 * x^2 + 4 * y^2 + 9 * z^2) then
            1
          else 0

-- Sanity checks from the problem description, kept as stubs.
theorem a_zero : A271513 0 = 1 := by sorry
theorem a_one : A271513 1 = 3 := by sorry
theorem a_two : A271513 2 = 2 := by sorry
theorem a_three : A271513 3 = 1 := by sorry

-- Definition of the set of exceptional numbers $S$ for Conjecture (i).
def unique_counts_set_A271513_base : Finset ℕ :=
  {0, 3, 11, 23, 43, 47, 67, 83, 107, 155, 323, 683, 803}

def belongs_to_unique_counts_set_A271513 (n : ℕ) : Prop :=
  n ∈ unique_counts_set_A271513_base ∨ ∃ k : ℕ, (n = 4^k * 22 ∨ n = 4^k * 38)

/--
Conjecture (i): a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 3, 11, 23, 43, 47, 67, 83, 107, 155, 323, 683, 803, 4^k*m (k = 0,1,2,... and m = 22, 38).
-/
theorem A271513_conjecture_i (n : ℕ) :
  A271513 n > 0 ∧ (A271513 n = 1 ↔ belongs_to_unique_counts_set_A271513 n) :=
by sorry

-- Predicate for Conjecture (ii) and (iii)
/--
A natural number n can be written as a sum of four squares $w^2 + x^2 + y^2 + z^2$
such that $a x^2 + b y^2 + c z^2$ is a square, where $w, x, y, z$ are integers.
Note: $a, b, c$ are implicitly positive integers from the context of the conjecture.
-/
def has_lagrange_square_refinement (n a b c : ℕ) : Prop :=
  a > 0 ∧ b > 0 ∧ c > 0 ∧ ∃ w x y z : ℤ,
    (w^2 + x^2 + y^2 + z^2 : ℤ) = n ∧ ∃ s : ℤ, a * x^2 + b * y^2 + c * z^2 = s^2

/--
The set of triples $(a, b, c)$ mentioned in Conjecture (ii).
We use ℕ since $a, b, c$ are positive integers.
-/
def A271513_suitable_triples : Finset (ℕ × ℕ × ℕ) :=
  {
    (1, 3, 12), (1, 3, 18), (1, 3, 21), (1, 3, 60), (1, 5, 15), (1, 8, 24),
    (1, 12, 15), (1, 24, 56), (1, 24, 72), (1, 48, 72), (1, 48, 168), (1, 120, 180),
    (1, 192, 288), (1, 280, 560), (3, 9, 13), (4, 5, 12), (4, 5, 60), (4, 9, 60),
    (4, 12, 21), (4, 12, 45), (4, 12, 69), (4, 12, 93), (4, 12, 237), (4, 21, 24),
    (4, 21, 36), (4, 21, 504), (4, 24, 93), (4, 28, 77), (4, 45, 120), (4, 45, 540),
    (4, 45, 600), (5, 36, 40), (7, 9, 126), (7, 9, 588), (8, 16, 73), (8, 16, 97),
    (8, 49, 112), (9, 13, 27), (9, 16, 24), (9, 19, 36), (9, 21, 91), (9, 24, 232),
    (9, 28, 63), (9, 40, 45), (9, 40, 56), (9, 40, 120), (9, 45, 115), (9, 45, 235),
    (12, 13, 24), (12, 13, 36), (12, 36, 37), (12, 36, 133), (13, 36, 72), (13, 36, 108),
    (15, 24, 25), (15, 49, 105), (16, 17, 48), (16, 20, 45), (16, 21, 84), (16, 33, 72),
    (16, 33, 176), (16, 45, 180), (16, 48, 57), (16, 48, 105), (16, 48, 233), (16, 48, 249),
    (19, 45, 57), (19, 45, 180), (21, 25, 35), (21, 25, 75), (21, 28, 36), (21, 28, 60),
    (21, 43, 105), (21, 100, 105), (24, 25, 72), (24, 25, 120), (24, 48, 97), (24, 81, 184),
    (24, 120, 145), (25, 36, 75), (25, 40, 56), (25, 45, 51), (25, 45, 99), (25, 48, 96),
    (25, 48, 144), (25, 54, 90), (25, 75, 81), (25, 80, 184), (25, 96, 120), (25, 200, 216),
    (28, 33, 36), (28, 36, 77), (28, 72, 189), (32, 64, 73), (33, 36, 220), (33, 48, 144),
    (33, 72, 256), (33, 88, 144), (36, 45, 100), (36, 45, 172), (37, 81, 243), (40, 81, 120),
    (40, 81, 240), (41, 64, 256), (45, 48, 76), (48, 144, 177), (49, 56, 64), (49, 63, 72),
    (55, 141, 165), (57, 64, 192), (60, 105, 196), (64, 65, 160), (72, 73, 144), (81, 160, 240),
    (85, 140, 196), (105, 112, 144), (112, 144, 153), (136, 144, 153), (144, 145, 240), (144, 160, 225),
    (148, 189, 252), (175, 189, 225)
  }

/--
Conjecture (ii): Any natural number can be written as $w^2 + x^2 + y^2 + z^2$ with $x, y, z$ integers
and $a x^2 + b y^2 + c z^2$ a square, whenever $(a,b,c)$ is among the listed triples.
-/
theorem A271513_conjecture_ii :
  ∀ (a b c : ℕ), (a, b, c) ∈ A271513_suitable_triples → ∀ n : ℕ, has_lagrange_square_refinement n a b c :=
by sorry

/--
Conjecture (iii): If a, b and c are positive integers such that any natural number can be written as w^2 + x^2 + y^2 + z^2 with x, y, z integers and a*x^2 + b*y^2 + c*z^2 a square, then a, b and c cannot be pairwise coprime.
-/
theorem A271513_conjecture_iii (a b c : ℕ) :
  (a > 0 ∧ b > 0 ∧ c > 0) →
  ( (∀ n : ℕ, has_lagrange_square_refinement n a b c) →
    ¬ (Nat.gcd a b = 1 ∧ Nat.gcd a c = 1 ∧ Nat.gcd b c = 1) ) :=
by sorry

/--
See also A271510 and A271518 for related conjectures.
-/
theorem oeis_271513_conjecture_3 : True :=
by sorry
