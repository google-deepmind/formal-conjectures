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
import FormalConjecturesForMathlib.Geometry.«2d»

/-!
# Erdős Problem 735

*Reference:* [erdosproblems.com/735](https://www.erdosproblems.com/735)

Given any $n$ points in $\mathbb{R}^2$, when can one assign positive weights to the points
such that the sum of the weights along every line containing at least two points
is the same?

A problem of Murty, who conjectured this is only possible in one of four cases:
1. All points on a line
2. No three points on a line (general position)
3. $n - 1$ points on a line (with one point off)
4. The 7-point incenter configuration: a triangle, the feet of the three angle
   bisectors, and the incenter (or a projective equivalence)

Proved by Ackerman, Buchin, Knauer, Pinchasi, and Rote [ABKPR08].

*Acknowledgement:* Noga Alon.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
  Combinatorica 1 (1981), 25–42.

[ABKPR08] Ackerman, E., Buchin, K., Knauer, C., Pinchasi, R., and Rote, G.,
_There are not too many magic configurations_, Discrete & Computational Geometry 39 (2008), 3--16.
-/

open Finset BigOperators Classical EuclideanGeometry

open scoped EuclideanGeometry

namespace Erdos735

/-- A finite set of points in $\mathbb{R}^2$ admits a balanced weighting if there exist positive
real weights such that the total weight on every line through $\geq 2$ points is the same. -/
noncomputable def AdmitsBalancedWeighting (S : Finset ℝ²) : Prop :=
  ∃ (w : ℝ² → ℝ),
    (∀ p ∈ S, w p > 0) ∧
    ∀ p₁ ∈ S, ∀ q₁ ∈ S, ∀ p₂ ∈ S, ∀ q₂ ∈ S,
      p₁ ≠ q₁ → p₂ ≠ q₂ →
      ∑ x ∈ S.filter (fun x => Collinear ℝ ({p₁, q₁, x} : Set ℝ²)), w x =
      ∑ x ∈ S.filter (fun x => Collinear ℝ ({p₂, q₂, x} : Set ℝ²)), w x

/-- All points of $S$ are collinear (lie on a single line). -/
def AllCollinear (S : Finset ℝ²) : Prop :=
  Collinear ℝ (↑S : Set ℝ²)

/-- All but one point of $S$ are collinear, and the full set is not collinear. -/
def AllButOneCollinear (S : Finset ℝ²) : Prop :=
  ∃ p ∈ S, Collinear ℝ (↑(S.erase p) : Set ℝ²) ∧ ¬Collinear ℝ (↑S : Set ℝ²)

/-- The 7-point incenter configuration of a non-degenerate triangle $ABC$: the three vertices,
the incenter, and the three feet of the angle bisectors. Two 7-point sets have the same
incidence structure if there is a bijection between them that preserves collinearity of triples.

`HasIncenterIncidenceStructure S` holds when $S$ has the same collinearity incidence pattern
as some incenter configuration — equivalently, $S$ is a projective image of an incenter
configuration where all 7 points remain finite. -/
noncomputable def HasIncenterIncidenceStructure (S : Finset ℝ²) : Prop :=
  ∃ (A B C : ℝ²),
    ¬Collinear ℝ ({A, B, C} : Set ℝ²) ∧ (
      let a := dist B C
      let b := dist C A
      let c := dist A B
      let bisA := (b / (b + c)) • B + (c / (b + c)) • C
      let bisB := (a / (a + c)) • A + (c / (a + c)) • C
      let bisC := (a / (a + b)) • A + (b / (a + b)) • B
      let inc := (a / (a + b + c)) • A + (b / (a + b + c)) • B + (c / (a + b + c)) • C
      let T : Finset ℝ² := {A, B, C, bisA, bisB, bisC, inc}
      ∃ f : ℝ² → ℝ²,
        Function.Bijective f ∧
        (S.image f = T ∨ S = T) ∧
        ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
          Collinear ℝ ({p, q, r} : Set ℝ²) ↔
          Collinear ℝ ({f p, f q, f r} : Set ℝ²))

/--
Erdős Problem 735 (Murty's conjecture, proved by Ackerman–Buchin–Knauer–Pinchasi–Rote [ABKPR08]):

A finite set $S$ of at least 2 points in $\mathbb{R}^2$ admits a balanced weighting if and only if
$S$ is one of:
1. All points collinear,
2. No three points collinear (general position),
3. All but one point collinear, or
4. A 7-point configuration with the same incidence structure as the incenter configuration
   (i.e., the incenter configuration or a projective equivalence).
-/
@[category research solved, AMS 5 52]
theorem erdos_735 (S : Finset ℝ²) (hS : 2 ≤ S.card) :
    AdmitsBalancedWeighting S ↔
      AllCollinear S ∨ NonTrilinear (↑S : Set ℝ²) ∨ AllButOneCollinear S ∨
      HasIncenterIncidenceStructure S := by
  sorry

end Erdos735
