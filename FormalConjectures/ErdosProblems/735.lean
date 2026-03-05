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

[ABKPR08] Ackerman, E., Buchin, K., Knauer, C., Pinchasi, R., and Rote, G.,
_There are not too many magic configurations_, Discrete & Computational Geometry 39 (2008), 3--16.
-/

open Finset BigOperators Classical

namespace Erdos735

/-- The Euclidean plane. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- A finite set of points in $\mathbb{R}^2$ admits a balanced weighting if there exist positive
real weights such that the total weight on every line through $\geq 2$ points is the same. -/
noncomputable def AdmitsBalancedWeighting (S : Finset R2) : Prop :=
  ∃ (w : R2 → ℝ),
    (∀ p ∈ S, w p > 0) ∧
    ∀ p₁ ∈ S, ∀ q₁ ∈ S, ∀ p₂ ∈ S, ∀ q₂ ∈ S,
      p₁ ≠ q₁ → p₂ ≠ q₂ →
      ∑ x ∈ S.filter (fun x => Collinear ℝ ({p₁, q₁, x} : Set R2)), w x =
      ∑ x ∈ S.filter (fun x => Collinear ℝ ({p₂, q₂, x} : Set R2)), w x

/-- All points of $S$ are collinear (lie on a single line). -/
def AllCollinear (S : Finset R2) : Prop :=
  Collinear ℝ (↑S : Set R2)

/-- No three points of $S$ are collinear ($S$ is in general position). -/
def NoThreeCollinear (S : Finset R2) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    p ≠ q → q ≠ r → p ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set R2)

/-- All but one point of $S$ are collinear, and the full set is not collinear. -/
def AllButOneCollinear (S : Finset R2) : Prop :=
  ∃ p ∈ S, Collinear ℝ (↑(S.erase p) : Set R2) ∧ ¬Collinear ℝ (↑S : Set R2)

/-- The 7-point incenter configuration: vertices $A$, $B$, $C$ of a non-degenerate triangle,
the incenter, and the three feet of the angle bisectors from $A$, $B$, $C$ to the
opposite sides. Here $a = |BC|$, $b = |CA|$, $c = |AB|$. The foot from $A$ to $BC$
divides $BC$ in the ratio $c : b$ (by the angle bisector theorem), and similarly
for the other feet. The full classification includes projective equivalences. -/
noncomputable def IsIncentreConfiguration (S : Finset R2) : Prop :=
  ∃ (A B C : R2),
    ¬Collinear ℝ ({A, B, C} : Set R2) ∧ (
      let a := dist B C
      let b := dist C A
      let c := dist A B
      let bisA := (b / (b + c)) • B + (c / (b + c)) • C
      let bisB := (a / (a + c)) • A + (c / (a + c)) • C
      let bisC := (a / (a + b)) • A + (b / (a + b)) • B
      let inc := (a / (a + b + c)) • A + (b / (a + b + c)) • B + (c / (a + b + c)) • C
      S = ({A, B, C, bisA, bisB, bisC, inc} : Finset R2))

/--
Erdős Problem 735 (Murty's conjecture, proved by Ackerman–Buchin–Knauer–Pinchasi–Rote [ABKPR08]):

A finite set $S$ of at least 2 points in $\mathbb{R}^2$ admits a balanced weighting if and only if
$S$ is one of:
1. All points collinear,
2. No three points collinear (general position),
3. All but one point collinear, or
4. The 7-point incenter configuration (or a projective equivalence).
-/
@[category research solved, AMS 5 52]
theorem erdos_735 (S : Finset R2) (hS : 2 ≤ S.card) :
    AdmitsBalancedWeighting S ↔
      AllCollinear S ∨ NoThreeCollinear S ∨ AllButOneCollinear S ∨
      IsIncentreConfiguration S := by
  sorry

end Erdos735
