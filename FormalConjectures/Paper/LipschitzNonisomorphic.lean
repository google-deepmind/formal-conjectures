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
# Lipschitz equivalent Banach spaces need not be linearly isomorphic

*Reference:* OpenAI, *Lipschitz Equivalent Separable Banach Spaces Need Not Be
Linearly Isomorphic* (2026), Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lipschitz-Equivalent-Separable-Banach-Spaces-Need-Not-Be-Linearly-Isomorphic-September-24-2026/paper.pdf
-/

@[expose] public section

namespace LipschitzNonisomorphic

/-- There are separable real Banach spaces with a bi-Lipschitz bijection of lower
bound $4/21$ and upper bound $76/25$, but no continuous real-linear isomorphism. -/
@[category research solved, AMS 46]
theorem exists_nonisomorphic_pair :
    ∃ (X Y : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X)
      (_ : NormedAddCommGroup Y) (_ : NormedSpace ℝ Y),
      CompleteSpace X ∧ CompleteSpace Y ∧
        TopologicalSpace.SeparableSpace X ∧ TopologicalSpace.SeparableSpace Y ∧
        ∃ Ψ : X ≃ Y,
          (∀ s t : X, (4 / 21 : ℝ) * ‖s - t‖ ≤ ‖Ψ s - Ψ t‖ ∧
            ‖Ψ s - Ψ t‖ ≤ (76 / 25 : ℝ) * ‖s - t‖) ∧
          IsEmpty (X ≃L[ℝ] Y) := by
  sorry

end LipschitzNonisomorphic
