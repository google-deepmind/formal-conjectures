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

/--
It is known that for any entire function $f$ and any fixed $m$, the zero set of the $m$-th
derivative $f^{(m)}$ is either finite or dense (by the identity theorem for holomorphic functions).
The question asks about sequences of derivatives simultaneously having dense zero sets.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/906", AMS 30]
theorem erdos_906.variants.known_result :
    ∀ (f : ℂ → ℂ), Differentiable ℂ f → ∀ m : ℕ,
      (∃ z, iteratedDeriv m f z = 0) →
      Dense { z | iteratedDeriv m f z = 0 } ∨
      { z | iteratedDeriv m f z = 0 }.Finite := by
  sorry

end Erdos906
