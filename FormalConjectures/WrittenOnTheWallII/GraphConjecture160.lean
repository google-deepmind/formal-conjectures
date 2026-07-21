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
# Written on the Wall II - Conjecture 160

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a vertex $v$ in $G$, **$T(v)$** is the number of triangles incident to $v$:
$$T(v) = |\{\{u, w\} \subseteq N(v) \mid u \sim w\}|$$
i.e., the number of pairs of neighbors of $v$ that are themselves adjacent.

The invariant `maxTrianglesAtVertex G` is the maximum of $T(v)$ over all vertices.

Conjecture 160 uses both $\max_v T(v)$ and $\chi_{C_4}(G)$, the $C_4$-free
characteristic function: it is `1` when $G$ contains no cycle of length four
and `0` otherwise. The cycle need not be induced. These invariants lower-bound
the WOWII invariant $L_s(G)$, the maximum number of leaves over all spanning
trees of $G$ (exposed as `SimpleGraph.Ls G : ℝ`).

The earlier formalization used the number of induced four-cycles. The historical
conjecture instead uses this binary $C_4$-free indicator.

**Provenance.** Corrected by Dominic Dabish. ProofOrchestrator, using OpenAI
GPT-5.6 Thinking, assisted with source comparison and Lean formalization; the
corrected statement was checked by the pinned Lean compiler.
-/

namespace WrittenOnTheWallII.GraphConjecture160

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The maximum number of triangles incident to any vertex in $G$. -/
noncomputable def maxTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (numTrianglesAtVertex G)).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/--
WOWII [Conjecture 160](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$L_s(G) \ge \max_v l(v) + \max_v T(v) \cdot \chi_{C_4}(G)$
where:

- $L_s(G) = \mathrm{SimpleGraph.Ls}\, G$ is the maximum number of leaves over all
  spanning trees of $G$,
- $\max_v l(v)$ is the maximum local independence number over vertices,
- $\max_v T(v)$ is the maximum number of triangles incident to any vertex,
- $\chi_{C_4}(G)$ is `1` if $G$ has no cycle of length four and `0` otherwise.
-/
@[category research open, AMS 5]
theorem conjecture160 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    let maxT := maxTrianglesAtVertex G
    let cC4 : ℕ := if ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4 then 0 else 1
    (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G := by
  sorry

-- Sanity checks

/-- In $K_3$, every vertex has $1$ triangle incident to it. -/
@[category test, AMS 5]
example : numTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) (0 : Fin 3) = 1 := by
  unfold numTrianglesAtVertex
  decide +native

/-- In $K_3$, `maxTrianglesAtVertex = 1`. -/
@[category test, AMS 5]
example : maxTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) = 1 := by
  unfold maxTrianglesAtVertex numTrianglesAtVertex
  decide +native

/-- In the path $P_3$, vertex $1$ is adjacent to $0$ and $2$, but $0$ and $2$ are not adjacent.
So $T(1) = 0$. -/
@[category test, AMS 5]
example : numTrianglesAtVertex
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) (1 : Fin 3) = 0 := by
  unfold numTrianglesAtVertex
  decide +native

end WrittenOnTheWallII.GraphConjecture160
