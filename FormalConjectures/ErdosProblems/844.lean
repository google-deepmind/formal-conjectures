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
# Erdős Problem 844

*References:*
- [erdosproblems.com/844](https://www.erdosproblems.com/844)
- [AMS25] Alexeev, B., Mixon, D. and Sawin, W., *The independence and clique cover numbers of the
  squarefree graph*. arXiv:2507.01928 (2025).
- [Ch74] Chvátal, V., *Intersecting families of edges in hypergraphs having the hereditary
  property*. (1974), 61-66.
-/

namespace Erdos844

/-- Those $n \in \{1,\ldots,N\}$ which are even or not squarefree, that is, the set of even
numbers together with the odd non-squarefree numbers. -/
def evenOrOddNonSquarefree (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => 2 ∣ n ∨ ¬ Squarefree n)

/--
Let $A\subseteq \{1,\ldots,N\}$ be such that, for all $a,b\in A$, the product $ab$ is not
squarefree.

Is the maximum size of such an $A$ achieved by taking $A$ to be the set of even numbers and
odd non-squarefree numbers?

A problem of Erdős and Sárközy.

Weisenberg has provided the following positive proof. It is clear that such a maximal $A$ must
contain all non-squarefree numbers. It therefore suffices to find the largest size of a subset
of all squarefree numbers in $\{1,\ldots,N\}$ such that any two have at least one prime factor
in common. By the result of Chvátal [Ch74] discussed in [701] this is maximised by the set of
all even squarefree numbers.

An alternative proof was independently found by Alexeev, Mixon, and Sawin [AMS25].
-/
@[category research solved, AMS 5 11]
theorem erdos_844 : answer(True) ↔ ∀ N : ℕ,
    IsGreatest {k : ℕ | ∃ A ⊆ Finset.Icc 1 N,
      (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) ∧ A.card = k}
      (evenOrOddNonSquarefree N).card := by
  sorry

end Erdos844
