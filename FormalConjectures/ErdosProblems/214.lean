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
# Erdős Problem 214

*References:*
- [erdosproblems.com/214](https://www.erdosproblems.com/214)
- [CsTo94] Csizmadia, Gy\"orgy and T\'oth, G\'eza, *Note on a {R}amsey-type
  problem in geometry*. J. Combin. Theory Ser. A (1994), 302--306.
- [EGMRSS75] Erd\H{o}s, P. and Graham, R. L. and Montgomery, P. and Rothschild,
  B. L. and Spencer, J. and Straus, E. G., *Euclidean {R}amsey theorems.
  {II}*. (1975), 529--557.
- [Ju79] Juh\'{a}sz, Roz\'{a}lia, *Ramsey type theorems in the plane*.
  J. Combin. Theory Ser. A (1979), 152-160.
-/

open scoped EuclideanGeometry

namespace Erdos214

abbrev Point := ℝ²

/-- The four vertices of a unit square. -/
noncomputable def unitSquare : Fin 4 → Point :=
  ![0, EuclideanSpace.single 0 1,
    EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1,
    EuclideanSpace.single 1 1]

/-- Two indexed configurations are congruent if they have the same pairwise distances. -/
def CongruentConfiguration (P Q : Fin 4 → Point) : Prop :=
  ∀ i j, dist (P i) (P j) = dist (Q i) (Q j)

/-- A set contains four points which form a unit square. -/
def ContainsUnitSquare (S : Set Point) : Prop :=
  ∃ sq : Fin 4 → Point, CongruentConfiguration unitSquare sq ∧ ∀ i, sq i ∈ S

/--
Let $S\subset \mathbb{R}^2$ be such that no two points in $S$ are distance $1$ apart. Must the complement of $S$ contain four points which form a unit square?

Juh\'{a}sz [Ju79] answered this affirmatively.
-/
@[category research solved, AMS 5 51,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos214.lean"]
theorem erdos_214 : answer(True) ↔
    ∀ S : Set Point, (∀ P ∈ S, ∀ Q ∈ S, dist P Q ≠ 1) → ContainsUnitSquare Sᶜ := by
  sorry

end Erdos214
