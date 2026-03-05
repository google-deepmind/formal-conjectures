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
# Erdős Problem 215

*Reference:* [erdosproblems.com/215](https://www.erdosproblems.com/215)

Does there exist a set $S \subseteq \mathbb{R}^2$ such that every set congruent to $S$
contains exactly one point of $\mathbb{Z}^2$? The answer is yes, proved by Jackson and
Mauldin [JaMa02] using the axiom of choice.

[JaMa02] Jackson, S. and Mauldin, R.D., _On a lattice problem of H. Steinhaus_, Journal of the
American Mathematical Society 15 (2002), 817-856.
-/

namespace Erdos215

/--
The integer lattice $\mathbb{Z}^2 \subseteq \mathbb{R}^2$: points whose coordinates are all
integers.
-/
def IntLattice : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i : Fin 2, ∃ n : ℤ, p i = ↑n}

/--
Erdős Problem 215 (Steinhaus Problem):
Does there exist $S \subseteq \mathbb{R}^2$ such that every set congruent to $S$
(that is, $S$ after some isometry) contains exactly one point from $\mathbb{Z}^2$?

The answer is yes, proved by Jackson and Mauldin [JaMa02].
Their construction depends on the axiom of choice.
-/
@[category research solved, AMS 52]
theorem erdos_215 : answer(True) ↔
    ∃ (S : Set (EuclideanSpace ℝ (Fin 2))),
      ∀ (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
        Isometry f →
        ∃! p, p ∈ f '' S ∧ p ∈ IntLattice := by
  sorry

end Erdos215
