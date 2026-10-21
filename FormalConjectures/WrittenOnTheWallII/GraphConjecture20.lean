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
module

public import FormalConjecturesUtil
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

/-!
# Written on the Wall II - Conjecture 20

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [AKS87] N. Alon, J. Kahn and P. D. Seymour, [Large Induced Degenerate Subgraphs](https://doi.org/10.1007/BF01788542), Graphs and Combinatorics 3 (1987), 203–211.
- [Li26] Wentao Li, [Lean proof of WOWII 20](https://github.com/VictorLiwentao/lean-graph-proofs/blob/9ce66be23570e0a9c8a6ae3f19f52e642878a8a9/proofs/WOWII20/PROOF.md), 2026.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture20

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 20](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, `b(G) ≥ n(G) / ⌊deg_avg(G)⌋`, where `b(G)` is
the size of a largest induced bipartite subgraph, `n(G)` is the number of vertices,
and `deg_avg(G) = (∑ v, deg(v)) / n(G)` is the average degree.

Follows from the weighted induced-subgraph bound of Alon, Kahn and Seymour [AKS87].
Lean formalization by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-graph-proofs/blob/9ce66be23570e0a9c8a6ae3f19f52e642878a8a9/LeanGraphProofs/WOWII20.lean#L499"]
theorem conjecture20 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let deg_avg : ℝ := (∑ v : α, (G.degree v : ℝ)) / (Fintype.card α : ℝ)
    (Fintype.card α : ℝ) / (⌊deg_avg⌋ : ℝ) ≤ (b G : ℝ) := by
  sorry

-- Sanity checks

/-- The number of vertices of `K₃` is 3. -/
@[category test, AMS 5]
example : Fintype.card (Fin 3) = 3 := by decide

/-- The average degree of `K₃` is 2 (every vertex has degree 2 in the complete graph on 3 vertices). -/
@[category test, AMS 5]
example : averageDegree (⊤ : SimpleGraph (Fin 3)) = 2 := by
  unfold averageDegree; simp [Fintype.card_fin]

end WrittenOnTheWallII.GraphConjecture20
