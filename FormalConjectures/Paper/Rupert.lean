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

namespace Rupert

open scoped Matrix

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

scoped notation "ℝ²" => Fin 2 → ℝ
scoped notation "ℝ³" => Fin 3 → ℝ

/--
The result of transforming a subset of ℝ³ by a chosen rotation and offset,
and then projected to ℝ².
--/
def transformed_shadow (X : Set ℝ³) (offset : ℝ²) (rotation : SO3) : Set ℝ² :=
  (fun p ↦ offset + (rotation *ᵥ p) ∘ Fin.castSucc) '' X

/--
A convex polyhedron (given as a finite collection of vertices) is Rupert if
there are two rotations in ℝ³ (called "inner" and "outer") and a translation in ℝ²
such that the "inner shadow" (the projection to ℝ² of the inner rotation applied
to the polyhedron, then translated) fits in the interior of the "outer shadow"
(the projection to ℝ² of the outer rotation applied to the polyhedron)

[Note: The restriction to (polyhedra determined by the convex hulls of)
*finite* sets of vertices here is deliberate. Were we to generalize to
arbitrary subsets of ℝⁿ we'd probably want to make the containment
relation more strict, e.g.
  closure inner_shadow ⊆ interior outer_shadow
to rule out, e.g. the open ball being Rupert. However, we didn't
observe any such generalization in the literature yet, so we stuck to
what was in the citations above.]
-/
def IsRupert (vertices : Finset ℝ³) : Prop :=
   ∃ (inner_rotation : SO3) (inner_offset : ℝ²) (outer_rotation : SO3),
   let inner_shadow := transformed_shadow (convexHull ℝ vertices) inner_offset inner_rotation
   let outer_shadow := transformed_shadow (convexHull ℝ vertices) 0 outer_rotation
   inner_shadow ⊆ interior outer_shadow

/--
Does the Rupert property hold for every convex polyhedron with nonempty interior?
-/
@[category research open, AMS 52]
theorem is_every_convex_polyhedron_rupert :
    (∀ (vertices : Finset ℝ³),
       (interior (convexHull ℝ vertices : Set ℝ³)).Nonempty → IsRupert vertices)
      ↔ answer(sorry) := by
 sorry
