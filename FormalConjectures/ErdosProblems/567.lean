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
# Erdős Problem 567

Let $G$ be either $Q_3$ or $K_{3,3}$ or $H_5$ (the last formed by adding two vertex-disjoint chords
to $C_5$). Is it true that, if $H$ has $m$ edges and no isolated vertices, then
$$ \hat{r}(G,H) \ll m? $$

In other words, is $G$ Ramsey size linear? A special case of Problem 566.

*Reference:* [erdosproblems.com/567](https://www.erdosproblems.com/567)

[EFRS93] Erdős, Faudree, Rousseau and Schelp, _Ramsey size linear graphs_.
Combin. Probab. Comput. (1993), 389-399.
-/

namespace Erdos567

open SimpleGraph
open scoped Finset

/-- $Q_3$ is the 3-dimensional hypercube graph (8 vertices, 12 edges).
Vertices are 3-bit vectors. Two vertices are adjacent iff they differ in exactly one bit. -/
def Q3 : SimpleGraph (Fin 3 → Bool) where
  Adj u v := #{i | u i ≠ v i} = 1
  symm _ _ := by simp [eq_comm]
  loopless _ := by simp

/-- $K_{3,3}$ is the complete bipartite graph with partition sizes 3, 3 (6 vertices, 9 edges). -/
def K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- $H_5$ is $C_5$ with two vertex-disjoint chords (5 vertices, 7 edges).
Also known as $K_4^*$ (the graph obtained from $K_4$ by subdividing one edge). -/
def H5 : SimpleGraph (Fin 5) :=
  .cycleGraph 5 ⊔ .edge 0 2 ⊔ .edge 1 3

/--
**Erdős Problem 567 (Q3)**

Is $Q_3$ (the 3-dimensional hypercube) Ramsey size linear?
-/
@[category research open, AMS 05]
theorem erdos_567_Q3 : answer(sorry) ↔ IsRamseySizeLinear Q3 := by
  sorry

/--
**Erdős Problem 567 (K33)**

Is $K_{3,3}$ Ramsey size linear?
-/
@[category research open, AMS 05]
theorem erdos_567_K33 : answer(sorry) ↔ IsRamseySizeLinear K33 := by
  sorry

/--
**Erdős Problem 567 (H5)**

Is $H_5$ ($C_5$ with two vertex-disjoint chords) Ramsey size linear?
-/
@[category research open, AMS 05]
theorem erdos_567_H5 : answer(sorry) ↔ IsRamseySizeLinear H5 := by
  sorry

end Erdos567
