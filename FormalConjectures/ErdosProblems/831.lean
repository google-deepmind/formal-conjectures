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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 831

*References:*
- [erdosproblems.com/831](https://www.erdosproblems.com/831)
- [Er75h] Erdős, P., *Some problems on elementary geometry*. Austral. Math. Soc. Gaz. (1975), 2-3.
  [PDF](https://www.renyi.hu/~p_erdos/1975-41.pdf)
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*. Eureka
  (1992), 44-48.
-/

@[expose] public section

open Filter Asymptotics EuclideanGeometry

namespace Erdos831

/-- The set of radii of the circles passing through at least three points of `P`. A circle is a
`Sphere ℝ²` (a centre and a radius), and we collect the radii of those spheres that contain at
least three points of `P`. For a finite `P` this set is finite, since three distinct points lie on
at most one circle. -/
def circleRadii (P : Set ℝ²) : Set ℝ :=
  (fun s : Sphere ℝ² ↦ s.radius) '' {s : Sphere ℝ² | 3 ≤ {p ∈ P | p ∈ s}.ncard}

/-- The number of circles of different radii passing through three points of `P`. -/
noncomputable def numRadii (P : Set ℝ²) : ℕ :=
  (circleRadii P).ncard

/-- `h n` is the minimum, over all sets `P` of `n` points of the plane in general position (no
three on a line, no four on a circle), of the number `numRadii P` of different radii of circles
through three points of `P`. In Erdős's words, `h n` is the largest integer such that every such
`P` determines at least `h n` circles of different radii.

Admissible `P` exist for every `n`: the points $(i, i^2)$, $1 \le i \le n$, have no three on a
line, and four points $(t_j, t_j^2)$ of the parabola lie on a circle only if $\sum_j t_j = 0$.
Hence the set below is nonempty and `sInf` is a true minimum. For $n \le 2$ no circle passes
through three points and `h n = 0`. -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ P : Finset ℝ², P.card = n ∧ InGeneralPosition (P : Set ℝ²) ∧
    numRadii (P : Set ℝ²) = k}

/-- A set of `n` points in general position determining `k` different radii gives
`h n ≤ k`. -/
@[category API, AMS 51 52]
theorem h_le {n : ℕ} (P : Finset ℝ²) (hcard : P.card = n) (hP : InGeneralPosition (P : Set ℝ²)) :
    h n ≤ numRadii (P : Set ℝ²) :=
  Nat.sInf_le ⟨P, hcard, hP, rfl⟩

def erdos_831.answer : ℕ → ℝ := sorry

/--
Let $h(n)$ be maximal such that in any $n$ points in $\mathbb{R}^2$ (with no three on a line and
no four on a circle) there are at least $h(n)$ many circles of different radii passing through
three points. Estimate $h(n)$.

Erdős asks this in [Er75h, pp. 2-3] (see also [Er92e]); see also Problems 104 and 506. We read
"estimate" as the order of magnitude `=Θ`. [Er75h] also asks how $h(n)$ changes if one only
assumes that the points are not all on a circle; this is not formalised.
-/
@[category research open, question value, AMS 51 52]
theorem erdos_831 :
    (fun n : ℕ ↦ (h n : ℝ)) =Θ[atTop] erdos_831.answer := by
  sorry

/--
Erdős [Er75h, p. 2] attributes to E. Szekeres the observation that for three points
$x_1,x_2,x_3$ of the plane, not on a line, there is a unique point $x_4$ such that
$x_1,x_2,x_3,x_4$ are not on a circle and the four circles determined by the four triples of these
points have the same radius; one can take $x_4$ to be the orthocentre of the triangle
$x_1x_2x_3$.

Read literally this fails for a right-angled triangle, whose orthocentre is a vertex, so we assume
that the triangle has no right angle. We also require the four points to be in general position,
so that the four circles exist.
-/
@[category research solved, AMS 51 52]
theorem erdos_831.variants.szekeres (x₁ x₂ x₃ : ℝ²)
    (hcol : ¬ Collinear ℝ ({x₁, x₂, x₃} : Set ℝ²)) (hright : ¬ IsRightAngled x₁ x₂ x₃) :
    ∃! x₄ : ℝ², x₄ ∉ ({x₁, x₂, x₃} : Set ℝ²) ∧
      InGeneralPosition ({x₁, x₂, x₃, x₄} : Set ℝ²) ∧
      (circleRadii ({x₁, x₂, x₃, x₄} : Set ℝ²)).ncard = 1 := by
  sorry

end Erdos831
