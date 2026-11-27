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
# An operator without a nontrivial hyperinvariant subspace

*Reference:* OpenAI, *Backward intertwiners and a transitive commutant* (2026),
Corollary 1.2.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/paper.pdf
-/

@[expose] public section

namespace HyperinvariantSubspaces

open Filter
open scoped Topology

/-- Every separable infinite-dimensional complex Hilbert space has a nonzero
quasinilpotent operator whose only closed subspaces invariant under all commuting
bounded operators are the zero subspace and the whole space. -/
@[category research solved, AMS 46 47]
theorem exists_transitive_commutant
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (hInf : ¬ FiniteDimensional ℂ H) :
    ∃ T : H →L[ℂ] H, T ≠ 0 ∧
      Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
      ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
        (∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ K, A x ∈ K) →
        K = ⊥ ∨ K = ⊤ := by
  sorry

end HyperinvariantSubspaces
