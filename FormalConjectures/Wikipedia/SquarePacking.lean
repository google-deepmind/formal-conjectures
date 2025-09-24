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
# Square Packing

*References:*
- [Wikipedia on packing of squares in squares](https://en.wikipedia.org/wiki/Square_packing#In_a_square)
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
-/
def Square (side : ℝ) : Set ℝ² :=
  {p : ℝ² | 0 < p 0 ∧ p 0 < side ∧ 0 < p 1 ∧ p 1 < side}

/--
The unit square as a subset of the Euclidean plane
(not including border, so that squares that touch at the border are disjoint).
-/
def UnitSquare : Set ℝ² := Square 1

/--
A structure representing a packing of `n` isometric embeddings
of a set `s` inside a (presumably larger) set `S`.
-/
structure Packing (n : ℕ) (s : Set ℝ²) (S : Set ℝ²) where
  /-- The isometric equivalences
  that represent the transformations of the base shape to their locations in the packing. -/
  embeddings : Fin n → (ℝ² ≃ᵢ ℝ²)
  /-- The images of the embeddings are pairwise disjoint -/
  disjoint : ∀ i j : Fin n, i ≠ j → Disjoint (embeddings i '' s) (embeddings j '' s)
  /-- The images of the embeddings are all inside the larger set `S` -/
  inside : ∀ i : Fin n, embeddings i '' s ⊆ S

/--
Eleven unit squares can be packed into a square of side length < 3.877084.
-/
@[category undergraduate, AMS 51]
theorem square_packing_11_exists :
    Nonempty (Packing 11 UnitSquare (Square 3.877084)) := by
  sorry

/--
What is the smallest square that can contain 11 unit squares?
-/
@[category research open, AMS 51]
theorem least_square_packing_11 :
    IsLeast {x : ℝ | Nonempty (Packing 11 UnitSquare (Square x))} answer(sorry) := by
  sorry

/--
Seventeen unit squares can be packed into a square of side length < 4.6756.
-/
@[category undergraduate, AMS 51]
theorem square_packing_17_exists :
    Nonempty (Packing 17 UnitSquare (Square 4.6756)) := by
  sorry

/--
What is the smallest square that can contain 17 unit squares?
-/
@[category research open, AMS 51]
theorem least_square_packing_17 :
    IsLeast {x : ℝ | Nonempty (Packing 17 UnitSquare (Square x))} answer(sorry) := by
  sorry


end SquarePacking
