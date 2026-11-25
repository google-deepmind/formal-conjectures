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
module

public import FormalConjecturesUtil

/-!
# Magic Squares

*References:*

* [Magic Square of Squares - Wikipedia](https://en.wikipedia.org/wiki/Magic_square_of_squares)
* [multimagie.com](http://www.multimagie.com/English/SquaresOfSquaresSearch.htm)
* [Semi-Magic Square of Cubes](https://unsolvedproblems.org/index_files/SquareofCubes.htm)
* [Magic Square of Squares](https://static.nsta.org/pdfs/QuantumV6N3.pdf)
* [Ro96] Robertson, J. P. (1996). "Magic Squares of Squares". Mathematics Magazine 69 (4),
  289–293.
-/

@[expose] public section

namespace MagicSquares

/--
Does there exist a $3 \times 3$ matrix such that every entry is a distinct square,
and all rows, columns, and diagonals add up to the same value?

The entries are required to be positive. The other hypotheses already imply this:
see `IsMagicSquareOfSquares.pos`.
-/
@[category research open, question, AMS 11]
theorem exists_magic_square_squares :
    ∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
       m.Injective2 ∧
       (∀ i j, 0 < (m i j) ∧ IsSquare (m i j)) ∧
       (∀ i, ∑ j, m i j = t) ∧
       (∀ j, ∑ i, m i j = t) ∧
       m 0 0 + m 1 1 + m 2 2 = t ∧
       m 0 2 + m 1 1 + m 2 0 = t := by
  sorry

/-- `m` is a $3 \times 3$ magic square of squares with magic sum `t`: every entry is a
square, and the rows, columns and both diagonals sum to `t`. The entries need not be
distinct or positive. -/
structure IsMagicSquareOfSquares (m : Fin 3 → Fin 3 → ℕ) (t : ℕ) : Prop where
  isSquare : ∀ i j, IsSquare (m i j)
  row : ∀ i, ∑ j, m i j = t
  col : ∀ j, ∑ i, m i j = t
  diag : m 0 0 + m 1 1 + m 2 2 = t
  anti : m 0 2 + m 1 1 + m 2 0 = t

/-- A $3 \times 3$ array is primitive if no prime divides all nine entries. -/
def IsPrimitive (m : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ i j, ¬p ∣ m i j

/-- The magic sum of a $3 \times 3$ magic square of squares is three times the central
entry. -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Statement.lean#L122"]
theorem IsMagicSquareOfSquares.sum_eq {m : Fin 3 → Fin 3 → ℕ} {t : ℕ}
    (h : IsMagicSquareOfSquares m t) : t = 3 * m 1 1 := by
  sorry

/-- If the entries of a $3 \times 3$ magic square of squares are distinct, then they are
positive. Indeed, if one entry is $0$ then the opposite entry $y^2$ and the central entry
$e^2$ satisfy $y^2 = 2e^2$, so all nine entries are $0$. -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Statement.lean#L236"]
theorem IsMagicSquareOfSquares.pos {m : Fin 3 → Fin 3 → ℕ} {t : ℕ}
    (h : IsMagicSquareOfSquares m t) (hinj : m.Injective2) : ∀ i j, 0 < m i j := by
  sorry

/-- Every entry of a primitive $3 \times 3$ magic square of squares is of the form
$24k + 1$. -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Statement.lean#L146"]
theorem IsMagicSquareOfSquares.mod_twenty_four {m : Fin 3 → Fin 3 → ℕ} {t : ℕ}
    (h : IsMagicSquareOfSquares m t) (hprim : IsPrimitive m) : ∀ i j, m i j % 24 = 1 := by
  sorry

/-- The magic sum of a primitive $3 \times 3$ magic square of squares is of the form
$72k + 3$. -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Statement.lean#L157"]
theorem IsMagicSquareOfSquares.sum_mod_seventy_two {m : Fin 3 → Fin 3 → ℕ} {t : ℕ}
    (h : IsMagicSquareOfSquares m t) (hprim : IsPrimitive m) : t % 72 = 3 := by
  sorry

/-- No entry of a primitive $3 \times 3$ magic square of squares has a prime divisor of the
form $8k + 3$. -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Statement.lean#L163"]
theorem IsMagicSquareOfSquares.not_dvd_of_mod_eight_eq_three {m : Fin 3 → Fin 3 → ℕ} {t : ℕ}
    (h : IsMagicSquareOfSquares m t) (hprim : IsPrimitive m) {p : ℕ} (hp : p.Prime)
    (h8 : p % 8 = 3) : ∀ i j, ¬p ∣ m i j := by
  sorry

/-- Every prime divisor of the central entry of a primitive $3 \times 3$ magic square of
squares is of the form $4k + 1$. -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Statement.lean#L173"]
theorem IsMagicSquareOfSquares.mod_four_eq_one_of_dvd_center {m : Fin 3 → Fin 3 → ℕ} {t : ℕ}
    (h : IsMagicSquareOfSquares m t) (hprim : IsPrimitive m) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ m 1 1) : p % 4 = 1 := by
  sorry

/-- A $3 \times 3$ magic square of distinct squares exists if and only if there are three
arithmetic progressions of three squares, $x - n, x, x + n$ and $y - n, y, y + n$ and
$z - n, z, z + n$, with the same common difference $n$, whose middle terms $x, y, z$ form an
arithmetic progression, and whose nine terms are distinct [Ro96]. -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Statement.lean#L319"]
theorem exists_magic_square_squares_iff_three_progressions :
    (∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
       m.Injective2 ∧
       (∀ i j, 0 < (m i j) ∧ IsSquare (m i j)) ∧
       (∀ i, ∑ j, m i j = t) ∧
       (∀ j, ∑ i, m i j = t) ∧
       m 0 0 + m 1 1 + m 2 2 = t ∧
       m 0 2 + m 1 1 + m 2 0 = t) ↔
    ∃ x y z n : ℤ, x + z = 2 * y ∧
      IsSquare (x - n) ∧ IsSquare x ∧ IsSquare (x + n) ∧
      IsSquare (y - n) ∧ IsSquare y ∧ IsSquare (y + n) ∧
      IsSquare (z - n) ∧ IsSquare z ∧ IsSquare (z + n) ∧
      [x - n, x, x + n, y - n, y, y + n, z - n, z, z + n].Nodup := by
  sorry

/-- There exists a $4 \times 4$ magic square of distinct positive squares. This example is
due to Euler (1770). -/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/drew2apps/magic-square-of-squares-lean/blob/cda77a71ba6eceaca6739a0ec8e2c8a19462367c/MagicSquareOfSquares/Examples.lean#L77"]
theorem exists_magic_square_squares_four :
    ∃ m : Fin 4 → Fin 4 → ℕ, ∃ t : ℕ,
       m.Injective2 ∧
       (∀ i j, 0 < (m i j) ∧ IsSquare (m i j)) ∧
       (∀ i, ∑ j, m i j = t) ∧
       (∀ j, ∑ i, m i j = t) ∧
       ∑ i, m i i = t ∧
       ∑ i, m i i.rev = t := by
  sorry

/--
Does there exist a $3 \times 3$ semi-magic square whose entries are all distinct positive
integer cubes? A square is semi-magic if all rows and columns sum to the same total.

More precisely, we seek a $3 \times 3$ matrix with entries $a_{ij}$ such that each
$a_{ij} = n_{ij}^3$ for some positive integer $n_{ij}$, all nine cubes are distinct,
and all row sums and column sums are equal.

*Reference:*
[Semi-Magic Square of Cubes](https://unsolvedproblems.org/index_files/SquareofCubes.htm)
-/
@[category research open, question, AMS 5 11]
theorem exists_semi_magic_square_cubes :
    ∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
       m.Injective2 ∧
       (∀ i j, ∃ n : ℕ, 0 < n ∧ m i j = n ^ 3) ∧
       (∀ i, ∑ j, m i j = t) ∧
       (∀ j, ∑ i, m i j = t) := by
  sorry

end MagicSquares
