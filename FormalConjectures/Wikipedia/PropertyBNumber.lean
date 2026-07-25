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

import FormalConjectures.ErdosProblems.«602»

/-!
# The Property B Number

For an `n`-uniform finite hypergraph, Property B means that the vertices admit a two-colouring
with no monochromatic edge. The number `m(n)` is the minimum number of edges in an `n`-uniform
hypergraph without Property B.

*References:*
- [EL75] Erdős, Paul, and László Lovász. "Problems and results on 3-chromatic hypergraphs and some
  related questions." Infinite and Finite Sets (1975), 609-627.
  https://cs.nyu.edu/spencer/papers/french.pdf
- [GL24] Grill, Karl, and Daniel Linzmayer. "Improved Lower Bounds for Property B."
  https://arxiv.org/abs/2403.05674
- [Erdős Problems: Property B](https://mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/PropertyB.html)
-/

open Filter Set

namespace PropertyBNumber

/-- A finite family of finite sets is `n`-uniform if every member has cardinality `n`. -/
def IsNUniform {m v : ℕ} (n : ℕ) (A : Fin m → Finset (Fin v)) : Prop :=
  ∀ i, (A i).card = n

/-- Property B for a finite set system, using the general definition from Erdős Problem 602. -/
def HasPropertyB {m v : ℕ} (A : Fin m → Finset (Fin v)) : Prop :=
  Erdos602.HasPropertyB (Fin m) fun i ↦ (A i : Set (Fin v))

/-- An `n`-uniform finite set system that does not have Property B. -/
def IsCounterexample {m v : ℕ} (n : ℕ) (A : Fin m → Finset (Fin v)) : Prop :=
  IsNUniform n A ∧ ¬HasPropertyB A

/-- The possible edge counts of finite `n`-uniform hypergraphs without Property B. -/
def counterexampleSizes (n : ℕ) : Set ℕ :=
  {m | ∃ (v : ℕ) (A : Fin m → Finset (Fin v)), IsCounterexample n A}

/-- The Property B number `m(n)`: the minimum number of edges in an `n`-uniform hypergraph
without Property B. -/
noncomputable def propertyBNumber (n : ℕ) : ℕ :=
  sInf (counterexampleSizes n)

/-- The first Property B number is `m(1) = 1`. -/
@[category research solved, AMS 5]
theorem propertyBNumber_one : propertyBNumber 1 = 1 := by
  sorry

/-- The second Property B number is `m(2) = 3`. -/
@[category research solved, AMS 5]
theorem propertyBNumber_two : propertyBNumber 2 = 3 := by
  sorry

/-- The third Property B number is `m(3) = 7`. -/
@[category research solved, AMS 5]
theorem propertyBNumber_three : propertyBNumber 3 = 7 := by
  sorry

/-- The fourth Property B number is `m(4) = 23`. -/
@[category research solved, AMS 5]
theorem propertyBNumber_four : propertyBNumber 4 = 23 := by
  sorry

/-- The currently known bounds for the fifth Property B number are `29 ≤ m(5) ≤ 51`. -/
@[category research solved, AMS 5]
theorem propertyBNumber_five_bounds :
    29 ≤ propertyBNumber 5 ∧ propertyBNumber 5 ≤ 51 := by
  sorry

/-- Erdős and Lovász conjectured that `m(n) = Θ(n * 2^n)`. -/
@[category research open, AMS 5]
theorem erdos_lovasz_conjecture :
    answer(sorry) ↔
      (fun n : ℕ ↦ (propertyBNumber n : ℝ)) =Θ[atTop]
        (fun n : ℕ ↦ (n : ℝ) * 2 ^ n) := by
  sorry

end PropertyBNumber
