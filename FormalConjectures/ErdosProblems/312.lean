/-
Copyright 2025 The Formal Conjectures Authors

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

namespace Erdos312

noncomputable section
open scoped BigOperators

/--
Does there exist a constant `c > 0` such that for every `K > 1`, whenever the total
harmonic sum `∑ i, 1 / a i` exceeds `K` and `n` is large enough, we can choose a subset
of indices whose harmonic sum lies in `(1 - exp (-(c*K)), 1]`?
-/
@[category research open, AMS 5 11]
theorem erdos_312 :
  (∃ (c : ℝ), 0 < c ∧
    ∀ (K : ℝ), 1 < K →
      ∃ (N₀ : ℕ),
        ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ (∑ i : Fin n, (a i : ℝ)⁻¹) > K) →
            ∃ (S : Finset (Fin n)),
              1 - Real.exp (-(c * K)) < (∑ i in S, (a i : ℝ)⁻¹) ∧
              (∑ i in S, (a i : ℝ)⁻¹) ≤ 1)
  ↔ answer sorry := by
  sorry

end
end Erdos312
