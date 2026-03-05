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
# Erdős Problem 701

Chvátal's Conjecture: if a family of finite sets is downward closed (closed under taking subsets),
then the maximum size of an intersecting subfamily is at most the maximum degree (the largest
number of sets containing any single element).

*Reference:* [erdosproblems.com/701](https://www.erdosproblems.com/701)
-/

open Finset

namespace Erdos701

/-- A family of finite sets $\mathcal{F}$ is downward closed (an abstract simplicial complex)
if whenever $A \in \mathcal{F}$ and $B \subseteq A$, then $B \in \mathcal{F}$. -/
def IsDownwardClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B : Finset α, B ⊆ A → B ∈ F

/-- A family of finite sets $\mathcal{F}'$ is intersecting if every two members have
nonempty intersection. -/
def IsIntersectingFamily {α : Type*} [DecidableEq α] (F' : Finset (Finset α)) : Prop :=
  ∀ A ∈ F', ∀ B ∈ F', (A ∩ B).Nonempty

/--
Chvátal's Conjecture: Let $\mathcal{F}$ be a family of finite sets closed under taking subsets
(i.e. if $B \subseteq A \in \mathcal{F}$ then $B \in \mathcal{F}$). There exists some element $x$
such that whenever $\mathcal{F}' \subseteq \mathcal{F}$ is an intersecting subfamily we have
$|\mathcal{F}'| \leq |\{A \in \mathcal{F} : x \in A\}|$.

Equivalently, the maximum intersecting subfamily of a downward-closed family has size at most the
maximum degree.
-/
@[category research open, AMS 5]
theorem erdos_701 {α : Type*} [DecidableEq α] [Nonempty α]
    (F : Finset (Finset α))
    (hF : IsDownwardClosed F) :
    ∃ x : α, ∀ F' : Finset (Finset α), F' ⊆ F → IsIntersectingFamily F' →
      F'.card ≤ (F.filter (fun A => x ∈ A)).card := by
  sorry

end Erdos701
