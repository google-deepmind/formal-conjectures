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
# Vaught conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Vaught_conjecture)
-/

namespace VaughtConjecture

open FirstOrder.Language

/-- The number of countable models of some L-Theory T up to isomorhpism -/
def numberOfCountableModels {L : FirstOrder.Language} (T : L.Theory) : Cardinal :=
  Cardinal.mk (Quotient (Setoid.comap
    (fun (model : {mt : T.ModelType // Countable mt.Carrier}) ↦
    CategoryTheory.Bundled.mk model.val.Carrier model.val.struc)
    equivSetoid))

/--
The Vaught conjecture states that for a countable language L and a complete L-Theory T
the number of countable models of T (up to isomorphism) is finite, $\aleph_0$ or $2^{\aleph_0}$.
-/
@[category research open, AMS 3]
theorem vaught_conjecture {L : FirstOrder.Language} (hL : Countable L.Symbols)
                          {T : L.Theory} (hT : T.IsComplete) :
  numberOfCountableModels T ≤ Cardinal.aleph0 ∨ numberOfCountableModels T = Cardinal.continuum
  := by sorry

end VaughtConjecture
