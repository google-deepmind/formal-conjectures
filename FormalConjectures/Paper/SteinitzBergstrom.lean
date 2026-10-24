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
# The Euclidean Steinitz–Bergström bound

*Reference:* OpenAI, *The Euclidean Steinitz–Bergström theorem* (2026), Theorems 1.1
and 1.2.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026.pdf
-/

@[expose] public section

namespace SteinitzBergstrom

/-- One absolute constant bounds every signed prefix of a prescribed sequence of
Euclidean unit-ball vectors by $C\sqrt d$. The same constant bounds every unsigned
prefix after a permutation when the vectors sum to zero. Repeated and zero vectors
are allowed. -/
@[category research solved, AMS 46 52]
theorem signed_and_reordered_prefix_bounds :
    ∃ C : ℝ,
      (∀ d N : ℕ, 1 ≤ d → 1 ≤ N →
        ∀ v : Fin N → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ ≤ 1) →
          ∃ ε : Fin N → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
            ∀ k : ℕ, k ≤ N →
              ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), ε i • v i‖ ≤
                C * Real.sqrt d) ∧
      (∀ d N : ℕ, 1 ≤ d → 1 ≤ N →
        ∀ v : Fin N → EuclideanSpace ℝ (Fin d),
          (∀ i, ‖v i‖ ≤ 1) → (∑ i, v i) = 0 →
            ∃ π : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
              ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v (π i)‖ ≤
                C * Real.sqrt d) := by
  sorry

end SteinitzBergstrom
