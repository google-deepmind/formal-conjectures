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

import FormalConjecturesUtil

/-!
# Erdős Problem 181

*Reference:* [erdosproblems.com/181](https://www.erdosproblems.com/181)
-/

namespace Erdos181

open SimpleGraph

/-- The diagonal Ramsey number of a finite graph `G`: the least `N` such that every red-blue
colouring of the edges of the complete graph on `N` vertices contains a monochromatic copy of `G`.
A graph `R` records the red edges, and `Rᶜ` records the blue edges. -/
noncomputable def diagonalRamseyNumber {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  sInf {N : ℕ | ∀ R : SimpleGraph (Fin N), G.IsContained R ∨ G.IsContained Rᶜ}

/--
Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$ edges). Prove that $$R(Q_n) \ll 2^n.$$
-/
@[category research open, AMS 5]
theorem erdos_181 :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (diagonalRamseyNumber (hypercube n) : ℝ) ≤ C * 2 ^ n := by
  sorry

end Erdos181
