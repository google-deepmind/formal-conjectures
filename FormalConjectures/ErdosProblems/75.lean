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
# Erdős Problem 75

*Reference:*
* [erdosproblems.com/75] (https://www.erdosproblems.com/75)
-/

open Cardinal

namespace Erdos75

/--
Is there a graph of chromatic number `ℵ_ 1` with `ℵ_ 1` vertices such that for all
`ε > 0`, if `n` is sufficiently large and `H` is a subgraph on `n` vertices,
then `H` contains an independent set of size `> n ^ (1 - ε)`?
-/
@[category research open, AMS 05]
theorem erdos_75 :
    answer(sorry) ↔
    ∃ (V : Type) (G : SimpleGraph V),
      G.chromaticCardinal = ℵ_ 1 ∧
      #V = ℵ_ 1 ∧
      ∀ ε > (0 : ℝ),
        ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (H : G.Subgraph),
            H.verts.ncard = n →
            ∃ (I : Finset V),
              (I : Set V) ⊆ H.verts ∧
              G.IsIndepSet (I : Set V) ∧
              (I.card : ℝ) > (n : ℝ) ^ (1 - ε) := by
  sorry

end Erdos75
