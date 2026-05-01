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
# Erdős Problem 701

*Reference:* [erdosproblems.com/701](https://www.erdosproblems.com/701)
-/

namespace Erdos701

open Cardinal

/--
Let $\mathcal{F}$ be a family of sets closed under taking subsets (i.e. if
$B\subseteq A\in\mathcal{F}$ then $B\in \mathcal{F}$). There exists some element $x$ such that
whenever $\mathcal{F}'\subseteq \mathcal{F}$ is an intersecting subfamily we have
$$\lvert \mathcal{F}'\rvert \leq \lvert \{ A\in \mathcal{F} : x\in A\}\rvert.$$
-/
@[category research open, AMS 5]
theorem erdos_701 {X : Type*} [Nonempty X] :
    ∀ (F : Set (Set X)), IsLowerSet F →
      ∃ x : X, ∀ᵉ (F' ⊆ F),
        F'.Intersecting →
          (#F' ≤ #{ A : Set X | A ∈ F ∧ x ∈ A }) := by
  sorry

end Erdos701
