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
# Erdős Problem 1096
*Reference:* [erdosproblems.com/1096](https://www.erdosproblems.com/1096)
-/

open Filter

namespace Erdos1096

/-- The set of numbers of the shape ∑_{i ∈ S} q^i (for all finite S). -/
def Sums (q : ℝ) : Set ℝ :=
  { s | ∃ S : Finset ℕ, s = ∑ i ∈ S, q ^ i }

/--
Let 1 < q < 1 + ε and consider the set of numbers of the shape ∑_{i ∈ S} q^i
(for all finite S), ordered by size as 0 = x_1 < x_2 < ...
The sequence x is strictly increasing such that its range is Sums q.
If ε > 0 is sufficiently small, then x_{k+1} - x_k → 0.
-/
@[category research open, AMS 11]
theorem erdos_1096 :
    ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
    ∀ x : ℕ → ℝ, StrictMono x → Set.range x = Sums q →
    Tendsto (fun k => x (k + 1) - x k) atTop (nhds 0) ↔ answer(sorry) :=
  sorry

end Erdos1096
