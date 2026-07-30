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
# Written on the Wall II - Conjecture 109

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture109

open Classical SimpleGraph
/--
WOWII [Conjecture 109](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$, the independence number $\alpha(G)$ was
conjectured to satisfy
$\alpha(G) \le \lfloor (\mathrm{residue}(G) + 2 \cdot b(G)) / 3 \rfloor$, where
$\mathrm{residue}(G)$ is the Havel--Hakimi residue and $b(G)$ is the size of a
largest induced bipartite subgraph.

This is false. A connected graph on 21 vertices has an independent set of size
15, residue 8, and no induced bipartite subgraph with more than 18 vertices, so
the conjectured right-hand side is at most 14.

A smaller counterexample is the connected 13-vertex graph
$\overline K_7 \vee (K_3 \sqcup K_3)$. It has independence number $7$, residue
$2$, and largest induced bipartite subgraph size $9$, so its conjectured
right-hand side is $6$.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/DomTheDeveloper/formal-conjectures/blob/cf59008ef1cd432bf9803275dcf5d62ab1f094a3/FormalConjectures/WrittenOnTheWallII/GraphConjecture109.lean",
  formal_proof using lean4 at
    "https://github.com/chelokot/wowii-109-counterexample/blob/543a66ee78565b553f4ba6dc7fd32b5610557913/lean/GraphConjecture109.lean#L29-L139"]
theorem conjecture109 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
      (G.indepNum : ℝ) ≤ ⌊((residue G : ℝ) + 2 * b G) / 3⌋ := by
  sorry

-- Sanity checks

/-- The invariant `b G` is nonneg (cast of a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- The residue of $K_2$ equals $1$: degree sequence is $[1, 1]$; one Havel-Hakimi
step gives $[0]$, leaving a single zero. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 1 := by
  unfold residue
  decide +native

end WrittenOnTheWallII.GraphConjecture109
