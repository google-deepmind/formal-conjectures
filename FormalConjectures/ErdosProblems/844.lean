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
# Erdős Problem 844

*Reference:* [erdosproblems.com/844](https://www.erdosproblems.com/844)

A problem of Erdős and Sárközy [Er92b]. Proved affirmatively by Weisenberg,
and independently by Alexeev, Mixon, and Sawin [AMS25].

[Er92b] Erdős, P. and Sárközy, A., on products of elements not being squarefree (1992).

[AMS25] Alexeev, B., Mixon, D., and Sawin, W. (2025).
-/

namespace Erdos844

/-- The candidate extremal set for Erdős Problem 844: all numbers in
$\{1, \ldots, N\}$ that are either even or not squarefree. -/
noncomputable def extremalSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => Even n ∨ ¬Squarefree n)

/--
**Erdős Problem 844** [Er92b]:

Let $A \subseteq \{1, \ldots, N\}$ be such that for all $a, b \in A$, the product $ab$ is not
squarefree. Then $|A| \leq |\mathrm{extremalSet}(N)|$.

Equivalently, the maximum is achieved by the set of all even numbers together
with all odd non-squarefree numbers in $\{1, \ldots, N\}$.

Proved by Weisenberg, and independently by Alexeev, Mixon, and Sawin [AMS25].
-/
@[category research solved, AMS 11]
theorem erdos_844 :
    answer(True) ↔ ∀ (N : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      (∀ a ∈ A, ∀ b ∈ A, ¬Squarefree (a * b)) →
      A.card ≤ (extremalSet N).card := by
  sorry

end Erdos844
