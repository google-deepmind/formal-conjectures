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
# Written on the Wall II - Conjecture 63

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false for the lexicographic product $C_5[K_4]$. This graph
has minimum even-distance count $9$, while its largest induced forest and
largest induced bipartite subgraph both have order $4$. The conjectured lower
bound is therefore $\lceil(9 + 4 + 1)/3\rceil = 5 > 4$.
-/

namespace WrittenOnTheWallII.GraphConjecture63

open Classical SimpleGraph

/--
WOWII [Conjecture 63](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
asked whether every simple connected graph $G$ satisfies
$f(G) \geq \lceil(\min_v \operatorname{distEven}(v) + b(G) + 1)/3\rceil$.
The answer is no, as witnessed by $C_5[K_4]$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/Kuberwastaken/wowii-63-85-counterexample/blob/cba739842ec59adf7426c180009175b31935701d/lean/WOWII63.lean#L184-L195"]
theorem conjecture63 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      let minDistEven := (Finset.univ.image (G.distEven ·)).min' (by simp)
      ⌈((minDistEven : ℝ) + G.b + 1) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

/-- Every vertex is counted among the vertices at even distance from itself. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : 0 < G.distEven v := by
  unfold SimpleGraph.distEven
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨0, by simp [SimpleGraph.dist_self]⟩⟩⟩

end WrittenOnTheWallII.GraphConjecture63
