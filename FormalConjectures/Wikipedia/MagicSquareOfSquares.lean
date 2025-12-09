/-
Copyright 2025 The Formal Conjectures Authors.

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
# Magic Square of Squares

*References:*

* [Wikipedia](https://en.wikipedia.org/wiki/Magic_square_of_squares)
* [multimagie.com](http://www.multimagie.com/English/SquaresOfSquaresSearch.htm)
-/

namespace MagicSquareOfSquares

/--
Does there exist a 3 by 3 matrix such that every entry is a distinct square,
and all rows, columns, and diagonals add up to the same value?
-/
@[category research open, AMS 11]
theorem exists_magic_square_squares :
    (∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
       m.Injective2 ∧
       (∀ i j, IsSquare (m i j)) ∧
       ∀ i, ∑ j, m i j = t ∧
       ∀ j, ∑ i, m i j = t ∧
       m 0 0 + m 1 1 + m 2 2 = t ∧
       m 0 2 + m 1 1 + m 2 0 = t)
     ↔ answer(sorry) := by
  sorry

end MagicSquareOfSquares
