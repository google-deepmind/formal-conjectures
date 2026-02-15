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
# Erdős Problem 268

*Reference:*
 - [erdosproblems.com/268](https://www.erdosproblems.com/268)
 - [KoTa24] Kova\vC, V. and Tao T., On several irrationality problems for Ahmes series.
-/

namespace Erdos268

/-- Let `X` be the set of points in `Fin d → ℝ` of the shape
`fun i : Fin d => ∑' n : A, (1 : ℝ) / (n + i)` for some infinite subset `A ⊆ ℕ` such that
`1 / n` is summable over `A`. `X` has nonempty interior. This is proved in [KoTa24].
-/
@[category research solved, AMS 40 54]
theorem erdos_268 (d : ℕ) : (interior {x : Fin d → ℝ | ∃ A : Set ℕ, A.Infinite ∧
    Summable (fun n : A => (1 : ℝ) / n ) ∧
    x = fun i : Fin d => ∑' n : A, (1 : ℝ) / (n + i)}).Nonempty := by
  sorry

end Erdos268
