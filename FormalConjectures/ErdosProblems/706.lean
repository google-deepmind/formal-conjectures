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
# Erdős Problem 706

*Reference:* [erdosproblems.com/706](https://www.erdosproblems.com/706)

Let $L(r)$ be such that if $G$ is a graph formed by taking a finite set of points $P$ in
$\mathbb{R}^2$ and some set $A \subset (0,\infty)$ of size $r$, where the vertex set is $P$ and
there is an edge between two points if and only if their distance is a member of $A$, then
$\chi(G) \leq L(r)$.

The case $r = 1$ is the Hadwiger–Nelson problem, for which $5 \leq L(1) \leq 7$.

See also [508], [704], [705].
-/

namespace Erdos706

/-- The multi-distance graph in $\mathbb{R}^2$: given a set $A$ of positive reals, two points
are adjacent iff their Euclidean distance belongs to $A$. -/
noncomputable def multiDistanceGraph (A : Set ℝ) : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := x ≠ y ∧ dist x y ∈ A
  symm := fun _ _ ⟨hne, hd⟩ => ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := fun _ h => h.1 rfl

/--
Is it true that $L(r) \leq r^{O(1)}$? That is, does there exist a polynomial bound
on the chromatic number of multi-distance graphs in $\mathbb{R}^2$ as a function of the
number of allowed distances?

Formalized as: there exist constants $C, K \in \mathbb{N}$ such that for all $r \geq 1$ and all
sets $A$ of $r$ positive real distances, the multi-distance graph on $\mathbb{R}^2$ with
distance set $A$ is $(C \cdot r^K)$-colorable.
-/
@[category research open, AMS 5 51]
theorem erdos_706 : answer(sorry) ↔
    ∃ C K : ℕ, ∀ (r : ℕ), 1 ≤ r → ∀ (A : Finset ℝ), A.card = r →
    (∀ a ∈ A, (0 : ℝ) < a) →
    (multiDistanceGraph (↑A : Set ℝ)).Colorable (C * r ^ K) := by
  sorry

end Erdos706
