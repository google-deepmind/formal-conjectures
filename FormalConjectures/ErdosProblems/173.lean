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
# Erdős Problem 173

*References:*
- [erdosproblems.com/173](https://www.erdosproblems.com/173)
- [Sh76] Shader, L. E., *All right triangles are Ramsey in $E^2$!*. J. Combin. Theory Ser. A
  (1976), 385-389.
-/

@[expose] public section

open Affine
open scoped Congruent EuclideanGeometry

namespace Erdos173

/--
The colouring `c` contains a monochromatic triangle congruent to `T`.

Since `T'` is arbitrary, relabellings and reflections of `T` are allowed. Rescaling is not.
-/
def HasMonochromaticCopy (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ T' : Triangle ℝ ℝ², T'.points ≅ T.points ∧ ∃ i, ∀ j, c (T'.points j) = i

/--
In any $2$-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$ (up to
congruence), there is a monochromatic congruent copy of $T$.

The colouring is arbitrary. No measurability is assumed. `≅` compares vertices with the same
label, so the conclusion allows a relabelling `σ`.
-/
@[category research open, AMS 5 51]
theorem erdos_173 : answer(sorry) ↔ ∀ (c : ℝ² → Fin 2) (T₁ T₂ : Triangle ℝ ℝ²),
    ¬ HasMonochromaticCopy c T₁ → ¬ HasMonochromaticCopy c T₂ →
      ∃ σ : Equiv.Perm (Fin 3), T₁.points ∘ σ ≅ T₂.points := by
  sorry

/--
Shader [Sh76] proved that in any $2$-colouring of $\mathbb{R}^2$, every right-angled triangle
has a monochromatic congruent copy.
-/
@[category research solved, AMS 5 51]
theorem erdos_173.variants.right_triangle (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²)
    (hT : ∠ (T.points 0) (T.points 1) (T.points 2) = Real.pi / 2) :
    HasMonochromaticCopy c T := by
  sorry

/--
The exceptional triangle can exist: colouring the plane in alternating half-open strips of
suitable width gives no monochromatic copy of some equilateral triangle.
-/
@[category research solved, AMS 5 51]
theorem erdos_173.variants.equilateral_exception : ∃ (c : ℝ² → Fin 2) (T : Triangle ℝ ℝ²),
    dist (T.points 0) (T.points 1) = dist (T.points 1) (T.points 2) ∧
    dist (T.points 1) (T.points 2) = dist (T.points 2) (T.points 0) ∧
    ¬ HasMonochromaticCopy c T := by
  sorry

end Erdos173
