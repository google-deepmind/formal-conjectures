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
# Erdős Problem 963

*Reference:* [erdosproblems.com/963](https://www.erdosproblems.com/963)

[Er65] Erdős, P., _Extremal problems in number theory_, 1965.
-/

open Finset BigOperators

namespace Erdos963

/--
A finset of real numbers is *dissociated* if all subset sums are distinct:
for any two subsets $S$ and $T$ of $B$, if $\sum_{b \in S} b = \sum_{b \in T} b$ then $S = T$.
-/
def IsDissociated (B : Finset ℝ) : Prop :=
  ∀ S T, S ⊆ B → T ⊆ B → (∑ b ∈ S, b) = (∑ b ∈ T, b) → S = T

/--
Erdős Problem 963 [Er65]:

Let $f(n)$ be the maximal $k$ such that in any set $A \subset \mathbb{R}$ of size $n$ there is a
dissociated subset $B \subseteq A$ of size $|B| \geq k$ (i.e., all subset sums of $B$ are
distinct). Is it true that $f(n) \geq \lfloor \log_2 n \rfloor$?

Equivalently: for every finite set $A \subset \mathbb{R}$ of size $n$, there exists a dissociated
subset $B \subseteq A$ with $|B| \geq \lfloor \log_2 n \rfloor$.

Erdős noted that the greedy algorithm shows $f(n) \geq \lfloor \log_3 n \rfloor$.
-/
@[category research open, AMS 5]
theorem erdos_963 : answer(sorry) ↔ ∀ (A : Finset ℝ), A.Nonempty →
    ∃ B : Finset ℝ, B ⊆ A ∧ IsDissociated B ∧ Nat.log 2 A.card ≤ B.card := by
  sorry

end Erdos963
