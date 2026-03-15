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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 869

*Reference:* [erdosproblems.com/869](https://www.erdosproblems.com/869)

A question of Erdős and Nathanson.

[ErNa88] Erdős, P. and Nathanson, M.B., _Partitions of bases into disjoint unions of bases_,
J. Number Theory (1988), 1–9.

[Er92c] Erdős, P., _Some of my favourite problems in various branches of combinatorics_,
Matematiche (Catania) 47 (1992), no. 2, 231–240.
-/

namespace Erdos869

/--
**Erdős Problem 869** [ErNa88][Er92c]:

If $A_1$ and $A_2$ are disjoint additive bases of order $2$, must
$A_1 \cup A_2$ contain a minimal additive basis of order $2$?
-/
@[category research open, AMS 11]
theorem erdos_869 : answer(sorry) ↔
    ∀ (A₁ A₂ : Set ℕ), A₁.IsAsymptoticAddBasisOfOrder 2 → A₂.IsAsymptoticAddBasisOfOrder 2 →
    Disjoint A₁ A₂ →
    ∃ B : Set ℕ, B ⊆ A₁ ∪ A₂ ∧
      B.IsAsymptoticAddBasisOfOrder 2 ∧
      ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

end Erdos869
