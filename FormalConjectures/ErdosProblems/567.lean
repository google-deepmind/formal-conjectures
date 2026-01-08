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
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.SizeRamsey

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

/-- $Q_3$ is the 3-dimensional hypercube graph (8 vertices, 12 edges).
Vertices are 3-bit vectors. Two vertices are adjacent iff they differ in exactly one bit. -/
def Q3 : SimpleGraph (Fin 3 → Bool) :=
  SimpleGraph.fromRel fun a b => (Finset.univ.filter fun i => a i ≠ b i).card = 1

/-- $K_{3,3}$ is the complete bipartite graph with partition sizes 3, 3 (6 vertices, 9 edges). -/
def K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- $H_5$ is $C_5$ with two vertex-disjoint chords (5 vertices, 7 edges).
Edges: cycle 0-1-2-3-4-0 plus chords {0,2} and {1,3}. -/
def H5 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v =>
    -- Cycle C5 edges
    (u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val ∨
    -- Chord 0-2
    ({u, v} : Finset (Fin 5)) = {0, 2} ∨
    -- Chord 1-3
    ({u, v} : Finset (Fin 5)) = {1, 3}

/--
**Erdős Problem 567**

Let $G$ be either $Q_3$ or $K_{3,3}$ or $H_5$.
Is it true that $G$ is Ramsey size linear?
-/
@[category research open, AMS 05]
theorem erdos_567 : answer(sorry) ↔
    IsRamseySizeLinear Q3 ∧
    IsRamseySizeLinear K33 ∧
    IsRamseySizeLinear H5 := by
  sorry

end Erdos567
