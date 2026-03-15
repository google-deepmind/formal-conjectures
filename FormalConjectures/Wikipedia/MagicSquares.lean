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

/-!
# Magic Squares

*References:*

* [Magic Square of Squares - Wikipedia](https://en.wikipedia.org/wiki/Magic_square_of_squares)
* [multimagie.com](http://www.multimagie.com/English/SquaresOfSquaresSearch.htm)
* [Semi-Magic Square of Cubes](https://unsolvedproblems.org/index_files/SquareofCubes.htm)
-/

namespace MagicSquares

/--
Does there exist a $3 \times 3$ matrix such that every entry is a distinct square,
and all rows, columns, and diagonals add up to the same value?
-/
@[category research open, AMS 11]
theorem exists_magic_square_squares :
    answer(sorry) ↔ ∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
       m.Injective2 ∧
       (∀ i j, IsSquare (m i j)) ∧
       ∀ i, ∑ j, m i j = t ∧
       ∀ j, ∑ i, m i j = t ∧
       m 0 0 + m 1 1 + m 2 2 = t ∧
       m 0 2 + m 1 1 + m 2 0 = t := by
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
@[category research open, AMS 5 11]
theorem exists_semi_magic_square_cubes :
    answer(sorry) ↔ ∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
       m.Injective2 ∧
       (∀ i j, ∃ n : ℕ, 0 < n ∧ m i j = n ^ 3) ∧
       (∀ i, ∑ j, m i j = t) ∧
       (∀ j, ∑ i, m i j = t) := by
  sorry

end MagicSquares
