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

module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 64

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [J. J. Gebendorfer, Clique Blow-ups of the 5-Cycle and Written on the Wall II
  Conjecture 64](https://doi.org/10.5281/zenodo.21595503)

Gebendorfer recorded the disproof on 26 July 2026, crediting Kuberwastaken's
earlier $C_5[K_4]$ certificate for the graph and its induced-forest computation.
The linked Lean certificate formalizes this 20-vertex counterexample.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture64

open SimpleGraph

/--
WOWII Conjecture 64 proposed that every finite simple connected graph $G$ satisfies
$$
f(G) \geq \left\lceil\sqrt{\alpha(G)\bigl(1+(|V(G)|\bmod\Delta(G))\bigr)}\right\rceil,
$$
where $f(G)$ is the maximum order of an induced forest.
For $C_5[K_4]$, the forest number is $4$, the independence number is $2$,
and the proposed lower bound is $\lceil\sqrt{2(1+9)}\rceil=5$.

The remainder and product in the radicand are computed in $\mathbb{N}$ before
coercion to $\mathbb{R}$. Nontriviality excludes the one-vertex graph, whose
maximum degree is zero.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
"https://github.com/Kuberwastaken/c5-k4/blob/8c0a76079e5c7153bdc2dd6d97a9821ee25b2620/lean/GraphConjecture64.lean"]
theorem conjecture64 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
      ⌈Real.sqrt ((G.indepNum * (1 + Fintype.card α % G.maxDegree) : ℕ) : ℝ)⌉ ≤
        (G.largestInducedForestSize : ℝ) := by
  sorry

end WrittenOnTheWallII.GraphConjecture64
