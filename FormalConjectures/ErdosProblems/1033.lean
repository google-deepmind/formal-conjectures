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

import FormalConjecturesUtil
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

open scoped Classical
open Finset

/-!
# Erdős Problem 1033

*Reference:*
 - [erdosproblems.com/1033](https://www.erdosproblems.com/1033)
-/

namespace Erdos1033

/-- Let `h(n)` be the largest integer such that every graph on `n` vertices with more than
`n^2/4` edges contains a triangle whose three vertex degrees sum to at least `h(n)`.
Conjecture: `h(n) ≥ (2(√3 - 1) - o(1)) n`. This formalisation states the precise
asymptotic lower bound. -/
@[category research open, AMS 05C35]
theorem erdos_1033 : ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N →
    ∀ (G : SimpleGraph (Fin n)),
      (Finset.card (edgeFinset G) : ℝ) > ((n : ℝ)^2)/4 →
      (∃ (a b c : Fin n),
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        ((degree G a + degree G b + degree G c : ℝ) ≥ (2 * ((Real.sqrt 3) - 1) - ε) * (n : ℝ)))) :=
by
  sorry

end Erdos1033
