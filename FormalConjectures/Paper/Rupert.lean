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
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Is Every Convex Polyhedron Rupert?

A polyhedron is Rupert if one can cut a hole in it and pass another
copy of the same polyhedron through that hole.

More formally: a convex body in ℝ³ is a compact, convex set with
nonempty interior. A convex body X is said to be Rupert if there are
two affine transforms T₁, T₂ ∈ SE(3) such that π(T₁(X)) ⊆
int(π(T₂(X))), where π : ℝ³ → ℝ² is the evident projection, and int
denotes topological interior.

Not all convex bodies are Rupert. For example,
- the unit ball is not Rupert
- the circular cylinder of unit diameter and height
  closed on each end by disks is not Rupert

However, many convex polyhedra are Rupert. All Platonic solids, and
most Archimedean and Catalan solids are known to be Rupert.

Question: are all convex polyhedra with nonempty interior Rupert?

*References:*

* [Platonic Passages](https://www.researchgate.net/publication/314715434_Platonic_Passages),
  R. P. Jerrard, J. E. Wetzel, and L. Yuan., Math. Mag., 90(2):87–98,
  2017. conjectures ("with a certain hesitancy") that perhaps all
  convex polyhedra are Rupert.

* However, [An Algorithmic Approach to Rupert's Problem](https://arxiv.org/pdf/2112.13754#cite.JeWeYu17)
  describes experimental evidence to suggest that three Archimedean
  solids may not be Rupert.

* [Optimizing for the Rupert property](https://arxiv.org/abs/2210.00601)
  is the source of some of the Catalan solid results, and has more
  results for Johnson polyhedra as well.

* [This video by David Renshaw](https://www.youtube.com/watch?v=evKFok65t_E) visualizes
  known results for Platonic, Archimedean, and Catalan solids.

* This problem's name comes from the fact that it is a generalization
  of [Prince Rupert's Cube](https://en.wikipedia.org/wiki/Prince_Rupert%27s_cube).

-/
open scoped Matrix

notation "ℝ³" => Fin 3 → ℝ
notation "ℝ²" => Fin 2 → ℝ

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/--
The projection of a vector from 3-space to 2-space by dropping the third coordinate.
-/
def proj_xy (v : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![v 0, v 1]

/--
The result of transforming a subset of ℝ³ by a chosen rotation and offset,
and then projected to ℝ².
--/
def transformed_shadow (X : Set ℝ³) (offset : ℝ²) (rotation : SO3) : Set ℝ² :=
  (λ p ↦ offset + proj_xy (rotation.1 *ᵥ p)) '' X

/--
Get the "inner shadow" of a set of vertices, given the rotation and offset for it.
--/
def inner_shadow_of_vertices {ι : Type} [Fintype ι] (vertices : ι → ℝ³)
  (inner_offset : ℝ²) (inner_rotation : SO3) : Set ℝ² :=
  transformed_shadow (convexHull ℝ { vertices i | i }) inner_offset inner_rotation

/--
Get the "outer shadow" of a set of vertices, given the rotation and offset for it.
The outer shadow asymmetrically doesn't require a translation, since it would be
redundant to specify two, since translation commutes with projection.
--/
def outer_shadow_of_vertices {ι : Type} [Fintype ι] (vertices : ι → ℝ³)
  (outer_rotation : SO3) : Set ℝ² :=
  transformed_shadow (convexHull ℝ { vertices i | i }) 0 outer_rotation

/--
A convex polyhedron (given as a finite collection of vertices) is Rupert if
there are two rotations in ℝ³ (called "inner" and "outer") and a translation in ℝ²
such that the "inner shadow" (the projection to ℝ² of the inner rotation applied
to the polyhedron, then translated) fits in the interior of the "outer shadow"
(the projection to ℝ² of the outer rotation applied to the polyhedron)
-/
def IsRupert {ι : Type} [Fintype ι] (vertices : ι → ℝ³) : Prop :=
   ∃ (inner_rotation : SO3) (inner_offset : ℝ²) (outer_rotation : SO3),
   let inner_shadow := inner_shadow_of_vertices vertices inner_offset inner_rotation
   let outer_shadow := outer_shadow_of_vertices vertices outer_rotation
   inner_shadow ⊆ interior outer_shadow

/--
Does the Rupert property hold for every convex polyhedron with nonempty interior?
-/
@[category research open, AMS 52]
theorem is_every_convex_polyhedron_rupert :
    (∀ {ι : Type} [Fintype ι] (vertices : ι → ℝ³),
       (interior (convexHull ℝ { vertices i | i })).Nonempty → IsRupert vertices)
      ↔ answer(sorry) := by
 sorry
