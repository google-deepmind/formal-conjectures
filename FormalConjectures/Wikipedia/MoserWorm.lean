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
# Moser's Worm

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Moser%27s_worm_problem)
-/

open EuclideanGeometry MeasureTheory

/--
The set of worms is the set of curves of length (at most) 1.
We formalize this as the set of ranges of 1-Lipschitz functions from `[0,1]` to `ℝ²`.
-/
def Worms : Set (Set ℝ²) :=
    {s | ∃ f : (Set.Icc (0 : ℝ) (1 : ℝ)) → ℝ², LipschitzWith 1 f ∧ Set.range f = s}

/--
The set of covers is the set of (measurable) sets
that cover every worm by translation and rotation (i.e. through an isometry).
-/
def WormCovers : Set (Set ℝ²) :=
    {X | MeasurableSet X ∧ ∀ w ∈ Worms, ∃ iso, Isometry iso ∧ w ⊆ iso '' X}

/--
A disc of radius 1 / 2 is a worm cover.

This follows by translating the center of the disc to the midpoint of the worm.
-/
@[category high_school, AMS 52]
theorem disc_mem_worm_covers : Metric.closedBall 0 0.5 ∈ WormCovers := by
  sorry

/--
**Moser's Worm Problem**
What is the minimal area (or greatest lower bound on the area)
of a shape that can cover every unit-length curve?
-/
@[category research open, AMS 52]
theorem mosers_worm_problem :
    IsGLB {v | ∃ X ∈ WormCovers, volume X = v} answer(sorry) := by
  sorry

/--
There is a set of area 0.260437 that covers all worms.

*Reference:*
Norwood, Rick; Poole, George (2003), "An improved upper bound for Leo Moser's worm problem",
Discrete and Computational Geometry, 29 (3): 409–417, doi:10.1007/s00454-002-0774-3, MR 1961007.
-/
@[category research solved, AMS 52]
theorem mosers_worm_problem_upper_bound :
    ∃ X ∈ WormCovers, volume X = 0.260437 := by
  sorry

/--
**Convex Moser's Worm Problem**
What is the minimal area (or greatest lower bound on the area)
of a *convex* shape that can cover every unit-length curve?
-/
@[category research open, AMS 52]
theorem convex_mosers_worm_problem :
    IsGLB {v | ∃ X ∈ WormCovers, Convex ℝ X ∧ volume X = v} answer(sorry) := by
  sorry

/--
The minimal area of a convex shape that can cover every unit-length curve is attained.
This follows from the Blaschke selection theorem.
-/
@[category research solved, AMS 52]
theorem convex_mosers_worm_problem_bound_attained :
    ∃ bound, IsLeast {v | ∃ X ∈ WormCovers, Convex ℝ X ∧ volume X = v} bound := by
  sorry

/--
There is a convex set of area 0.270911861 that covers all worms.

*Reference:*
Wang, Wei (2006), "An improved upper bound for the worm problem",
Acta Mathematica Sinica, 49 (4): 835–846, MR 2264090.
-/
@[category research solved, AMS 52]
theorem convex_mosers_worm_problem_upper_bound :
    ∃ X : Set ℝ², MeasurableSet X ∧ Convex ℝ X ∧ volume X = 0.270911861 ∧
      ∀ w ∈ Worms, ∃ iso, Isometry iso ∧ w ⊆ iso '' X := by
  sorry

/--
0.232239 is a lower bound on the area of a convex set that covers all worms.

*Reference:*
Khandhawit, Tirasan; Pagonakis, Dimitrios; Sriswasdi, Sira (2013),
"Lower Bound for Convex Hull Area and Universal Cover Problems",
International Journal of Computational Geometry & Applications,
23 (3): 197–212, arXiv:1101.5638, doi:10.1142/S0218195913500076, MR 3158583, S2CID 207132316.
-/
@[category research solved, AMS 52]
theorem convex_mosers_worm_problem_lower_bound :
    0.232239 ∈ lowerBounds {v | ∃ X ∈ WormCovers, Convex ℝ X ∧ volume X = v} := by
  sorry
