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
# Erdős Problem 603

*Reference:* [erdosproblems.com/603](https://www.erdosproblems.com/603)

A problem of Komjáth [Er87]. Let $(A_i)$ be a family of countably infinite sets such that
$|A_i \cap A_j| \neq 2$ for all $i \neq j$. Find the smallest cardinal $C$ such that
$\bigcup A_i$ can always be coloured with at most $C$ colours so that no $A_i$ is
monochromatic. If instead we have $|A_i \cap A_j| \neq 1$ then Komjáth showed that this is
possible with at most $\aleph_0$ colours.

[Er87] Erdős, P., _Some problems on finite and infinite graphs_.
-/

open Cardinal Set

namespace Erdos603

/--
Erdős Problem 603 [Er87]:

Let $(A_i)$ be a family of countably infinite sets such that $|A_i \cap A_j| \neq 2$
for all $i \neq j$. Then there is a colouring with at most $\aleph_0$ colours so that
no $A_i$ is monochromatic.

This is conjectured by analogy with the Komjáth result for the $|A_i \cap A_j| \neq 1$
case, where $\aleph_0$ colours suffice.
-/
@[category research open, AMS 3 5]
theorem erdos_603 {α : Type*} {ι : Type*} (A : ι → Set α)
    (hcount : ∀ i, #(↥(A i)) = ℵ₀)
    (hne2 : ∀ i j, i ≠ j → (A i ∩ A j).ncard ≠ 2) :
    ∃ c : α → ℕ, ∀ i : ι, ∃ x ∈ A i, ∃ y ∈ A i, c x ≠ c y := by
  sorry

end Erdos603
