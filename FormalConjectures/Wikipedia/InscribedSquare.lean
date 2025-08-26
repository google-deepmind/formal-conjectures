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
# Inscribed square problem

The *inscribed square problem* or *Toeplitz conjecture* asks whether every Jordan curve (i.e. simple
close curve in ℝ²) admits an inscribed square, i.e. a square whose vertices all lie on the curve.
There are several open and solved variants of this conjecture.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Inscribed_square_problem)
 - [A Survey on the Square Peg Problem](https://www.researchgate.net/publication/274622766_A_Survey_on_the_Square_Peg_Problem)
   by *Benjamin Matschke*
 - [arxiv/2005.09193](https://arxiv.org/abs/2005.09193)
-/

open Topology ContDiff Manifold

/-- Four points `a b c d` in the plane form a rectangle  with `a` opposite to `c` iff the line
segments from `a` to `c` and from `b` to `d` have both the same length and the same midpoint, acting
as the diagonals of the rectangle. We also require the rectangle to be nondegenerate and have a
given aspect ratio `ratio : ℝ`. -/
structure IsRectangle (a b c d : EuclideanSpace ℝ (Fin 2)) (ratio : ℝ) : Prop where
  diagonal_midpoints_eq : a + c = b + d
  diagonal_lengths_eq : dist a c = dist b d
  a_ne_b : a ≠ b
  b_ne_c : b ≠ c
  has_ratio : (dist a b) / (dist b c) = ratio

/--
**Inscribed square problem**
Does every Jordan curve admit an inscribed square?
-/
@[category research open, AMS 51]
theorem inscribed_square_problem :
    (∀ (γ : Circle → EuclideanSpace ℝ (Fin 2)) (hγ : IsEmbedding γ),
      ∃ t₁ t₂ t₃ t₄, IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1) ↔ answer(sorry) :=
  sorry

/--
**Inscribed rectangle problem**
Does every Jordan curve admit inscribed rectangles of any given aspect ratio?
-/
@[category research open, AMS 51]
theorem inscribed_rectangle_problem :
    (∀ (γ : Circle → EuclideanSpace ℝ (Fin 2)) (hγ : IsEmbedding γ) (r : ℝ) (hr : r > 0),
      ∃ t₁ t₂ t₃ t₄, IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) r) ↔ answer(sorry) :=
  sorry

/--
It is known that every Jordan curve admits at least one inscribed rectangle.
-/
@[category research solved, AMS 51]
theorem exists_inscribed_rectangle (γ : Circle → EuclideanSpace ℝ (Fin 2)) (hγ : IsEmbedding γ) :
    ∃ t₁ t₂ t₃ t₄ r, IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) r :=
  sorry

/--
It is known that every *smooth* Jordan curve admits inscribed rectangles of all aspect ratios.
-/
@[category research solved, AMS 51]
theorem exists_inscribed_rectangle_of_smooth (γ : Circle → EuclideanSpace ℝ (Fin 2))
    (hγ : IsEmbedding γ) (hγ' : ContMDiff (𝓡 1) (𝓡 2) ∞ γ) (r : ℝ) (hr : r > 0) :
    ∃ t₁ t₂ t₃ t₄, IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) r :=
  sorry

/--
It is also known that every C² Jordan curve admits an inscribed square.
-/
@[category research solved, AMS 51]
theorem exists_inscribed_square_of_C2 (γ : Circle → EuclideanSpace ℝ (Fin 2))
    (hγ : IsEmbedding γ) (hγ' : ContMDiff (𝓡 1) (𝓡 2) 2 γ) :
    ∃ t₁ t₂ t₃ t₄, IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1 :=
  sorry
