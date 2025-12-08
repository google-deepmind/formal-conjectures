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
# Erdős Problem 1105

*Reference:* [erdosproblems.com/1105](https://www.erdosproblems.com/1105)
-/

namespace Erdos1105

/--
The anti-Ramsey number `AR(n, G)` is the maximum number of colours with which
the edges of the complete graph `K_n` can be coloured without creating a
rainbow copy of `G`.

This problem asks for the asymptotic behaviour of `AR(n, C_k)` for cycles `C_k`
and an exact formula for `AR(n, P_k)` for paths `P_k`.
-/

/- Conjecture for cycles `C_k`. -/
@[category research open, AMS 5 11]
axiom cycle_conjecture : Prop

/- Conjecture for paths `P_k`. -/
@[category research open, AMS 5 11]
axiom path_conjecture : Prop

/- Main bundled statement for Erdős Problem 1105. -/
@[category research open, AMS 5 11]
theorem erdos_1105.main :
    (cycle_conjecture ∧ path_conjecture) ↔ answer(sorry) := by
  sorry

end Erdos1105
