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
# Invariant Subspace Problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Invariant_subspace_problem)
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/--
Determine whether every bounded linear operator `T : H → H` in a separable Hilbert space `H` has a
non-trivial closed `T`-invariant subspace: a closed linear subspace `W` of `H`, which is different
from `{ 0 }` and from `H`, such that `T ( W ) ⊂ W`.-/
@[category research open, AMS 47]
theorem Invariant_subspace_problem (x : H →L[ℂ] H) : (∃ (S : Submodule ℂ H), S.carrier ≠ ∅ ∧
    S.carrier ≠ {0} ∧ S.carrier ≠ Set.univ ∧ IsClosed S.carrier ∧ ∀ v ∈ S, x v ∈ S.carrier) := by
 sorry
