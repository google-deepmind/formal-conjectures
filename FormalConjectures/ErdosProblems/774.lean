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
# Erdős Problem 774

*Reference:* [erdosproblems.com/774](https://www.erdosproblems.com/774)
-/

open Finset

/--
We call $A\subset \mathbb{N}$ dissociated if $\sum_{n\in X}n\neq \sum_{m\in Y}m$
for all finite $X,Y\subset A$ with $X\neq Y$.
-/
def Set.IsDissociated (A : Set ℕ) : Prop :=
  { S : Finset ℕ | (S : Set ℕ) ⊆ A }.InjOn fun S ↦ ∑ n ∈ S, n

/-- We call $A$ proportionately dissociated if every finite $B\subset A$
contains a dissociated set of size $\gg \lvert B\rvert$.

In other words, there is a (global) $c > 0$ such that every finite $B \subset A$
contains a dissociated set of size $\geq c|B|$. -/
def Set.IsProportionatelyDissociated (A : Set ℕ) : Prop :=
  ∃ c > (0 : ℝ), ∀ (B : Finset ℕ), (B : Set ℕ) ⊆ A →
    ∃ S ⊆ B, #S ≥ c * #B ∧ (S : Set ℕ).IsDissociated

namespace Erdos774

/-- Is every proportionately dissociated (infinite) set the union of a finite
number of dissociated sets?-/
@[category research open, AMS 5]
theorem erdos_774 : answer(sorry) ↔ ∀ (A : Set ℕ), A.Infinite → A.IsProportionatelyDissociated →
    ∃ (T : Set (Set ℕ)), (∀ S ∈ T, S.IsDissociated) ∧ T.Finite ∧ A = ⋃₀ T := by
  sorry

end Erdos774
