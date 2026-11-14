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
module

public import FormalConjecturesUtil
public import FormalConjectures.ErdosProblems.«508»

/-!
# The Hadwiger-Nelson Problem

The Hadwiger-Nelson problem asks for the minimum number of colors required to
color the plane such that no two points at unit distance from each other have
the same color.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hadwiger%E2%80%93Nelson_problem)
- [Ne02] Nechushtan, O., *On the space chromatic number*. Discrete Math. 256 (2002), 499-507.
  [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0012365X00004064)
- [Co02] Coulson, D., *A 15-colouring of 3-space omitting distance one*. Discrete Math. 256
  (2002), 83-90.
  [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0012365X01001832)

The planar problem is formalized in `FormalConjectures.ErdosProblems.«508»`. This file adds the
three-dimensional problem: the least number of colors needed to color $\mathbb{R}^3$ so that no
two points at distance $1$ have the same color.
-/

@[expose] public section

namespace HadwigerNelson

/-- The unit distance graph on $\mathbb{R}^3$: two points are adjacent if and only if the
distance between them is $1$. -/
def unitDistanceGraph3 : SimpleGraph (EuclideanSpace ℝ (Fin 3)) where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

/-- The origin and $(3/5, 4/5, 0)$ are adjacent. -/
@[category test, AMS 5 52]
theorem unitDistanceGraph3_three_four_five :
    unitDistanceGraph3.Adj 0 !₂[(3 : ℝ) / 5, (4 : ℝ) / 5, 0] := by
  norm_num [unitDistanceGraph3, EuclideanSpace.dist_eq, Fin.sum_univ_succ,
    Real.dist_eq, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- What is the chromatic number of three-dimensional space? -/
@[category research open, AMS 5 52]
theorem space_chromatic_number : unitDistanceGraph3.chromaticNumber = answer(sorry) := by
  sorry

/-- Nechushtan [Ne02] proved $\chi(\mathbb{R}^3) \ge 6$. -/
@[category research solved, AMS 5 52]
theorem space_chromatic_number_ge_six : 6 ≤ unitDistanceGraph3.chromaticNumber := by
  sorry

/-- Coulson [Co02] gave a $15$-coloring of $\mathbb{R}^3$ with no two points at distance $1$
of the same color, so $\chi(\mathbb{R}^3) \le 15$. -/
@[category research solved, AMS 5 52]
theorem space_chromatic_number_le_fifteen : unitDistanceGraph3.chromaticNumber ≤ 15 := by
  sorry

end HadwigerNelson
