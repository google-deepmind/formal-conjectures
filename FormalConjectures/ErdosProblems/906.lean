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
# Erdős Problem 906

*Reference:* [erdosproblems.com/906](https://www.erdosproblems.com/906)
-/

namespace Erdos906

/-- Does there exists an entire non-zero transcendental function `f : ℂ → ℂ` such that for any
sequence `n₀ < n₁ < ...`, `{ z | ∃ k, iteratedDeriv (n k) f z = 0 }` is dense. -/
@[category research open, AMS 30]
theorem erdos_906 : answer(sorry) ↔ ∃ f : ℂ → ℂ, Transcendental (Polynomial ℂ) f ∧
    Differentiable ℂ f ∧ ∀ n : ℕ → ℕ, StrictMono n →
    Dense { z | ∃ k, iteratedDeriv (n k) f z = 0 } := by
  sorry

end Erdos906
