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
# Erdős Problem 602

*Reference:* [erdosproblems.com/602](https://www.erdosproblems.com/602)

A problem of Komjáth. The existence of such a $2$-colouring is sometimes known as
Property B.

[Er87] Erdős, P., _Some problems and results on combinatorial number theory_.
-/

open Cardinal Set

namespace Erdos602

/-- Property B for a family of sets: there exists a $2$-colouring of the union
such that no set in the family is monochromatic (both colours appear). -/
def HasPropertyB {α : Type*} {ι : Type*} (A : ι → Set α) : Prop :=
  ∃ c : α → Bool, ∀ i : ι, (∃ x ∈ A i, c x = true) ∧ (∃ x ∈ A i, c x = false)

/--
Erdős Problem 602 [Er87]:

Let $(A_i)$ be a family of sets with $|A_i| = \aleph_0$ for all $i$, such that
for any $i \neq j$, $|A_i \cap A_j|$ is finite and $\neq 1$. Then the family
has Property B: there is a $2$-colouring of $\bigcup A_i$ such that no $A_i$ is
monochromatic.
-/
@[category research open, AMS 3 5]
theorem erdos_602 {α : Type*} {ι : Type*} (A : ι → Set α)
    (hcount : ∀ i, #(↥(A i)) = ℵ₀)
    (hfin : ∀ i j, i ≠ j → (A i ∩ A j).Finite)
    (hne1 : ∀ i j, i ≠ j → (A i ∩ A j).ncard ≠ 1) :
    HasPropertyB A := by
  sorry

end Erdos602
