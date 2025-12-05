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
# Erdős Problem 108

*Reference:* [erdosproblems.com/108](https://www.erdosproblems.com/108)
-/

universe u

namespace Erdos108

open Erdos108

/--
For every r ≥ 4 and k ≥ 2 is there some finite f(k,r) such that every graph of chromatic number ≥ f(k,r)
contains a subgraph of girth ≥ r and chromatic number ≥ k?
-/
@[category research open, AMS 5]
theorem erdos_108 :
    (∀ r ≥ 4, ∀ k ≥ (2 : ℕ), ∃ (f : ℕ),
    ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
      (hchro : f ≤ SimpleGraph.chromaticNumber G),
    ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
    (SimpleGraph.chromaticNumber H.coe ≥ k)) ↔ answer(sorry) := by
  sorry

-- TODO: Proof for the case r=4 and statement for the infinite case

end Erdos108
