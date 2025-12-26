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
# Earth-Moon Problem

The Earth-Moon problem asks for the maximum chromatic number of the union
of two planar graphs on the same set of vertices. This is equivalent to finding
the maximum chromatic number of graphs with thickness 2.

It is known that this number is between 9 and 12.
The conjecture is that the value is 9.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Earth-Moon_problem)
-/

namespace EarthMoonProblem

open SimpleGraph

/--
The precise statement of the Earth-Moon number for a specific graph pair.
It is the chromatic number of the union (lattice join) of two graphs.
-/
def earthMoonNumber {α : Type*} [Fintype α] [DecidableEq α] 
    (G₁ G₂ : SimpleGraph α) : ℕ :=
  (G₁ ⊔ G₂).chromaticNumber

/--
**Earth-Moon Conjecture**

The conjecture states that for any two planar graphs on any vertex set,
$9$ colors are sufficient to color their union.

This is an open problem. The current best lower bound is 9 (exhibited by $K_8$ plus a generic node, 
or by combining planar graphs to form $K_9$ edges minus some constraints), 
and the upper bound is 12.
-/
def EarthMoonConjecture : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α] (G₁ G₂ : SimpleGraph α),
    G₁.IsPlanar → G₂.IsPlanar → (G₁ ⊔ G₂).Colorable 9

end EarthMoonProblem

open EarthMoonProblem

/--
The formal statement of the Earth-Moon Conjecture.
-/
@[category research open, AMS 05C15]
theorem earth_moon_conjecture_nine : EarthMoonConjecture := by
  sorry
