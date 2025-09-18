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
# Erdős Problem 196

*Reference:* [erdosproblems.com/196](https://www.erdosproblems.com/196)
-/
namespace Erdos196

/-- Must every permutation of $\mathbb{N}$, contain a monotone 4-term arithmetic progression?-/
@[category research open, AMS 5 11]
theorem erdos_196 : (∀ (f : ℕ ≃ ℕ), ∃ (a : List ℕ),
    ((a.Sorted (· < · )) ∨ (a.Sorted (· > · ))) ∧ Set.IsAPOfLength (f '' a.toFinset) 4)
    ↔ answer(sorry) := by
  sorry

end Erdos196
