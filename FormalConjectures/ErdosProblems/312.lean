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
import FormalConjectures.Util.Answer.Syntax

namespace Erdos312

/--
Does there exist a constant $c > 0$ such that, for any $K > 1$, whenever $A$ is a sufficiently large finite multiset of integers with $\sum_{n\in A}\frac{1}{n}>K$ there exists some $S \subset A$ such that 
$$1-e^{-cK} < \sum_{n\in S}\frac{1}{n}\leq 1?$$
-/
theorem erdos_312 :
  (∃ (c : ℝ), 0 < c ∧
    ∀ (K : ℝ), 1 < K →
      ∃ (N₀ : ℕ),
        ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ (∑ i : Fin n, (a i : ℝ)⁻¹) > K) →
            ∃ (S : Finset (Fin n)),
              1 - Real.exp (-(c * K)) < (∑ i ∈ S, (a i : ℝ)⁻¹) ∧
              (∑ i ∈ S, (a i : ℝ)⁻¹) ≤ 1)
  ↔ answer sorry := by

end Erdos312
end ErdosProblems
end FormalConjectures
