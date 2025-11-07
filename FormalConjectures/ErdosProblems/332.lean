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
# Erdős Problem 332

*Reference:* [erdosproblems.com/332](https://www.erdosproblems.com/332)
-/

namespace Erdos332

open Set

/--
The set of numbers $D(A)$ which occur infinitely often as $a_1 - a_2$ with $a_1, a_2 \in A$.
-/
noncomputable def D_A (A : Set ℕ) : Set ℤ :=
  { d : ℤ | Set.Infinite { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = d } }

/--
A set $S \subseteq \mathbb{Z}$ has bounded gaps if it is syndetic, meaning there is a uniform
bound $M$ such that every interval of length $M$ contains an element of $S$.
-/
def HasBoundedGaps (S : Set ℤ) : Prop :=
  ∃ M : ℕ, M > 0 ∧ ∀ z : ℤ, ∃ s ∈ S, z ≤ s ∧ s < z + (M : ℤ)

/--
Let $A\subseteq \mathbb{N}$ and $D(A)$ be the set of those numbers which occur infinitely often as
$a_1 - a_2$ with $a_1, a_2\in A$. What conditions on $A$ are sufficient to ensure $D(A)$ has bounded
gaps?

This is formalised here using the `answer(sorry)` mechanism. In order to solve this problem one
has to provide what the sufficient conditions are, and proof that they imply the desired condition.
If the condition is a solution to the problem is up to human judgement.
-/
@[category research open, AMS 11]
theorem erdos_332 : ∀ (A : Set ℕ), (answer(sorry) : Set ℕ → Prop) A → HasBoundedGaps (D_A A) := by
  sorry

--TODO(firsching): formalize additional statements

end Erdos332
