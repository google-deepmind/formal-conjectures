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
# Packing

This file contains a number of open problems related to the minimal size of a square (or circle)
that can contain a given number of unit squares (or circles).
In each case, we provide a known upper bound, and ask for the least such size.

*References:*
- [Wikipedia on packing of squares](https://en.wikipedia.org/wiki/Square_packing)
- [Wikipedia on packing of circles in a circle](https://en.wikipedia.org/wiki/Circle_packing_in_a_circle)
- [Wikipedia on packing of circles in a square](https://en.wikipedia.org/wiki/Circle_packing_in_a_square)
- Friedman, Erich (2009), "Packing unit squares in squares: a survey and new results",
  Electronic Journal of Combinatorics, 1000, Dynamic Survey 7
- A website with visualizations of packings:
  [link](https://erich-friedman.github.io/packing/)
-/

open EuclideanGeometry

universe u

namespace SquarePacking

/--
A square of a particular side length as a subset of the Euclidean plane.
Not including border, so that squares that touch at the border are disjoint,
but a square internal to another shape is a subset of that shape.
-/
def Square (side : ℝ) : Set ℝ² :=
  {p : ℝ² | 0 < p 0 ∧ p 0 < side ∧ 0 < p 1 ∧ p 1 < side}

/--
The unit square as a subset of the Euclidean plane.
-/
def UnitSquare : Set ℝ² := Square 1

/--
A circle of a particular radius as a subset of the Euclidean plane.
Not including border, so that circles that touch at the border are disjoint,
but a circle internal to another shape is a subset of that shape.
-/
def Circle (r : ℝ) : Set ℝ² :=
  {p : ℝ² | p 0 ^ 2 + p 1 ^ 2 < r ^ 2}

/--
The unit circle as a subset of the Euclidean plane.
-/
def UnitCircle : Set ℝ² := Circle 1

/--
A structure representing a packing of `n` isometric embeddings
of a set `s` inside a (presumably larger) set `S`.
-/
structure Packing (n : ℕ) (s : Set ℝ²) (S : Set ℝ²) where
  /-- The isometric equivalences
  that represent the transformations of the base shape to their locations in the packing. -/
  embeddings : Fin n → (ℝ² ≃ᵢ ℝ²)
  /-- The images of the embeddings are pairwise disjoint -/
  disjoint : Pairwise fun i j => Disjoint (embeddings i '' s) (embeddings j '' s)
  /-- The images of the embeddings are all inside the larger set `S` -/
  inside : ∀ i : Fin n, embeddings i '' s ⊆ S

/--
Eleven unit squares can be packed into a square of side length < 3.877084.

Reference: [Wikipedia](https://en.wikipedia.org/wiki/Square_packing#In_a_square)
-/
@[category undergraduate, AMS 51]
theorem eleven_square_packing_in_square_bound :
    Nonempty (Packing 11 UnitSquare (Square 3.877084)) := by
  sorry

/--
What is the smallest square that can contain 11 unit squares?

Reference: [Wikipedia](https://en.wikipedia.org/wiki/Square_packing#In_a_square)
-/
@[category research open, AMS 51]
theorem least_eleven_square_packing_in_square :
    IsLeast {x : ℝ | Nonempty (Packing 11 UnitSquare (Square x))} answer(sorry) := by
  sorry

/--
Seventeen unit squares can be packed into a square of side length < 4.6756.

Reference: [Wikipedia](https://en.wikipedia.org/wiki/Square_packing#In_a_square)
-/
@[category undergraduate, AMS 51]
theorem seventeen_square_packing_in_square_bound :
    Nonempty (Packing 17 UnitSquare (Square 4.6756)) := by
  sorry

/--
What is the smallest square that can contain 17 unit squares?

Reference: [Wikipedia](https://en.wikipedia.org/wiki/Square_packing#In_a_square)
-/
@[category research open, AMS 51]
theorem least_seventeen_square_packing_in_square :
    IsLeast {x : ℝ | Nonempty (Packing 17 UnitSquare (Square x))} answer(sorry) := by
  sorry

/--
Three unit squares can be packed into a circle of radius (5 √17) / 16 ≈ 1.288.

Reference: [Wikipedia](https://en.wikipedia.org/wiki/Square_packing#In_a_circle)
-/
@[category undergraduate, AMS 51]
theorem three_square_packing_in_circle_bound :
    Nonempty (Packing 3 UnitSquare (Circle ((5 * √ 17) / 16))) := by
  sorry

/--
What is the smallest circle that can contain 3 unit squares?

Reference: [Wikipedia](https://en.wikipedia.org/wiki/Square_packing#In_a_circle)
-/
@[category research open, AMS 51]
theorem least_three_square_packing_in_circle :
    IsLeast {r : ℝ | Nonempty (Packing 3 UnitSquare (Circle r))} answer(sorry) := by
  sorry

/--
Twenty-one unit circles can be packed into a square of side length < 9.359.

Reference: [Visualizations](https://erich-friedman.github.io/packing/cirinsqu/)
-/
@[category undergraduate, AMS 51]
theorem twenty_one_circle_packing_in_square_bound :
    Nonempty (Packing 21 UnitCircle (Square 9.359)) := by
  sorry

/--
What is the smallest square that can contain 21 unit circles?
-/
@[category research open, AMS 51]
theorem least_twenty_one_circle_packing_in_square :
    IsLeast {x : ℝ | Nonempty (Packing 21 UnitCircle (Square x))} answer(sorry) := by
  sorry

/--
Fifteen unit circles can be packed into a circle of radius
1 + √ (6 + 2/√5 + 4 √(1 + 2/√5)) ≈ 4.521.

Reference:
Graham RL, Lubachevsky BD, Nurmela KJ, Ostergard PRJ.
Dense packings of congruent circles in a circle. Discrete Math 1998;181:139–154.
-/
@[category undergraduate, AMS 51]
theorem fifteen_circle_packing_in_circle_bound :
    Nonempty (Packing 15 UnitCircle (Circle (1 + √ (6 + 2 / √ 5 + 4 * √ (1 + 2 / √ 5)))) ) := by
  sorry

/--
What is the smallest circle that can contain 15 unit circles?

Reference:
Graham RL, Lubachevsky BD, Nurmela KJ, Ostergard PRJ.
Dense packings of congruent circles in a circle. Discrete Math 1998;181:139–154.
-/
@[category research open, AMS 51]
theorem least_fifteen_circle_packing_in_circle :
    IsLeast {r : ℝ | Nonempty (Packing 15 UnitCircle (Circle r))} answer(sorry) := by
  sorry

end SquarePacking
