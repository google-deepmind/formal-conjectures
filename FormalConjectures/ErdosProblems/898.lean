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
# Erdős Problem 898

If P is a point in the interior of triangle ABC, and D_a, D_b, D_c are the feet of the
perpendiculars from P to the sides BC, CA, AB respectively, then
PA + PB + PC ≥ 2(PD_a + PD_b + PD_c).

*Reference:* [erdosproblems.com/898](https://www.erdosproblems.com/898)

[Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_,
1982, pp. 59–79, p. 61.
-/

namespace Erdos898

/-- Squared Euclidean distance between two points in $\mathbb{R}^2$. -/
noncomputable def sqDist898 (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Euclidean distance between two points in $\mathbb{R}^2$. -/
noncomputable def dist898 (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist898 p q)

/-- A triangle is non-degenerate (vertices not collinear). -/
def NonDegenerate898 (A B C : ℝ × ℝ) : Prop :=
  (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) ≠ 0

/-- Point $P$ lies in the open interior of triangle $ABC$
(strictly positive barycentric coordinates). -/
def InInterior898 (P A B C : ℝ × ℝ) : Prop :=
  ∃ (α β γ : ℝ), 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    P.2 = α * A.2 + β * B.2 + γ * C.2

/-- The foot of the perpendicular from point $P$ to the line through $A$ and $B$.
This is the orthogonal projection of $P$ onto line $AB$:
$$\text{foot} = A + t \cdot (B - A)$$
where $t = \frac{(P - A) \cdot (B - A)}{|B - A|^2}$. -/
noncomputable def perpFoot898 (P A B : ℝ × ℝ) : ℝ × ℝ :=
  let dx := B.1 - A.1
  let dy := B.2 - A.2
  let t := ((P.1 - A.1) * dx + (P.2 - A.2) * dy) / (dx ^ 2 + dy ^ 2)
  (A.1 + t * dx, A.2 + t * dy)

/--
Erdős Problem 898 (Erdős-Mordell Inequality) [Er82e, p.61]:

If $A$, $B$, $C$ form a non-degenerate triangle in $\mathbb{R}^2$ and $P$ is a point in its
interior, then
$$
  d(P, A) + d(P, B) + d(P, C) \geq 2 \cdot (d(P, D_a) + d(P, D_b) + d(P, D_c))
$$
where $D_a$, $D_b$, $D_c$ are the feet of the perpendiculars from $P$ to sides
$BC$, $CA$, $AB$ respectively.

Conjectured by Erdős in 1932 and proved by Mordell soon afterwards.
-/
@[category research solved, AMS 51]
theorem erdos_898
    (A B C P : ℝ × ℝ)
    (hnd : NonDegenerate898 A B C)
    (hP : InInterior898 P A B C) :
    dist898 P A + dist898 P B + dist898 P C ≥
      2 * (dist898 P (perpFoot898 P B C) +
           dist898 P (perpFoot898 P A C) +
           dist898 P (perpFoot898 P A B)) := by
  sorry

end Erdos898
