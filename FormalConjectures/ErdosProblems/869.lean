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

[ErNa88] Erdős, P. and Nathanson, M., _Minimal asymptotic bases with prescribed densities_, 1988.
-/

namespace Erdos869

/-- The sumset $A + A$: the set of all $a + b$ with $a, b \in A$. -/
def sumset (A : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ A, n = a + b}

/-- A set $A \subseteq \mathbb{N}$ is an additive basis of order $2$ if every sufficiently large
    natural number can be written as $a + b$ with $a, b \in A$. -/
def IsAdditiveBasis2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → n ∈ sumset A

/-- A set $B \subseteq \mathbb{N}$ is a minimal additive basis of order $2$ if it is an additive
    basis of order $2$ and for every element $x \in B$, the set of natural numbers
    not in the sumset of $B \setminus \{x\}$ is infinite. -/
def IsMinimalAdditiveBasis2 (B : Set ℕ) : Prop :=
  IsAdditiveBasis2 B ∧
    ∀ x ∈ B, Set.Infinite {n : ℕ | n ∉ sumset (B \ {x})}

/--
**Erdős Problem 869** [ErNa88]:

If $A_1$ and $A_2$ are disjoint additive bases of order $2$, must
$A_1 \cup A_2$ contain a minimal additive basis of order $2$?
-/
@[category research open, AMS 11]
theorem erdos_869 : answer(sorry) ↔
    ∀ (A₁ A₂ : Set ℕ), IsAdditiveBasis2 A₁ → IsAdditiveBasis2 A₂ → Disjoint A₁ A₂ →
    ∃ B : Set ℕ, B ⊆ A₁ ∪ A₂ ∧ IsMinimalAdditiveBasis2 B := by
  sorry

end Erdos869
