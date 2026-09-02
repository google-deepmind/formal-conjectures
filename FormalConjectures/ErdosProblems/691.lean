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
# Erdős Problem 691

*Reference:* [erdosproblems.com/691](https://www.erdosproblems.com/691)
-/

namespace Erdos691

/-- The set $M_A = \{n \geq 1 : a \mid n \text{ for some } a \in A\}$ of positive multiples
of elements of $A$. -/
def multiples (A : Set ℕ) : Set ℕ := {n | 1 ≤ n ∧ ∃ a ∈ A, a ∣ n}

/-- Given $A \subseteq \mathbb{N}$, let
$M_A = \{n \geq 1 : a \mid n \text{ for some } a \in A\}$. Find a necessary and sufficient
condition on $A$ for $M_A$ to have density $1$. -/
@[category research open, AMS 11]
theorem erdos_691 :
    (answer(sorry) : Set ℕ → Prop) = fun A ↦ (multiples A).HasDensity 1 := by
  sorry

end Erdos691
