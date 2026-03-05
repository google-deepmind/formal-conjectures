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
# Erdős Problem 632

Erdős, Rubin, and Taylor asked whether $(a,b)$-choosability of a graph implies
$(am,bm)$-choosability for every positive integer $m$. Dvořák, Hu, and Sereni disproved this
by constructing a 4-choosable graph that is not $(8,2)$-choosable.

*Reference:* [erdosproblems.com/632](https://www.erdosproblems.com/632)

[ERT80] Erdős, P., Rubin, A.L., and Taylor, H., *Choosability in graphs*, Proceedings of the
West Coast Conference on Combinatorics, Graph Theory and Computing, Congressus Numerantium 26
(1980), 125-157.

[DHS19] Dvořák, Z., Hu, X., and Sereni, J.-S., *A 4-choosable graph that is not
(8:2)-choosable*, Advances in Combinatorics (2019).
-/

open SimpleGraph

namespace Erdos632

/-- A graph $G$ is $(a,b)$-choosable if for every assignment $L$ of a list of at least $a$
colors to each vertex, there exists a choice of a subset $S(v) \subseteq L(v)$ of size $b$
for each vertex $v$, such that the chosen subsets of adjacent vertices are disjoint. -/
def IsABChoosable {V : Type*} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, a ≤ (L v).card) →
    ∃ S : V → Finset ℕ, (∀ v, S v ⊆ L v) ∧ (∀ v, (S v).card = b) ∧
      (∀ u v, G.Adj u v → Disjoint (S u) (S v))

/--
Erdős Problem 632 [ERT80] (disproved by Dvořák, Hu, and Sereni [DHS19]):
If $G$ is $(a,b)$-choosable then $G$ is $(am, bm)$-choosable for every positive integer $m$.
-/
@[category research solved, AMS 5]
theorem erdos_632 : answer(False) ↔ ∀ (V : Type*) (G : SimpleGraph V) (a b m : ℕ),
    1 ≤ m → IsABChoosable G a b → IsABChoosable G (a * m) (b * m) := by
  sorry

end Erdos632
