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
# Erdős Problem 944

*Reference:* [erdosproblems.com/944](https://www.erdosproblems.com/944)
-/

universe u
variable {V : Type u}

namespace Erdos705

open Erdos705

-- {h : G.Adj = fun x y ↦ ‖x - y‖ = 1}
def unitDistanceGraph (G : SimpleGraph (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin 2), G.Adj x y ↔ ‖x - y‖ = 1

theorem erdos_705:
    (∀ (G : SimpleGraph (EuclideanSpace ℝ (Fin 2))) (h : unitDistanceGraph G),
        ∃ k, SimpleGraph.girth G ≥ k → SimpleGraph.chromaticNumber G ≤ 3) ↔ answer(sorry) := by
  sorry

end Erdos705
