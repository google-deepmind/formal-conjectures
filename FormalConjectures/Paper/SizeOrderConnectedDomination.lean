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
# Size, Order, and Connected Domination

*References:*
- [S. Mukwembi, _Size, order, and connected domination_,
  Canad. Math. Bull. 57 (2014), no. 1, 141–144](https://doi.org/10.4153/CMB-2013-020-5)
-/

namespace SizeOrderConnectedDomination

open SimpleGraph

/--
**Theorem 2.1** of [S. Mukwembi, _Size, order, and connected domination_,
Canad. Math. Bull. 57 (2014), no. 1, 141–144](https://doi.org/10.4153/CMB-2013-020-5)
claims: if $G$ is a connected triangle-free graph of order $n$ and size $m$ with
connected domination number $\gamma_c$, then
$$m \le \frac{(n - \gamma_c)^2}{4} + n - 1.$$

The claim is **false**: the 3-dimensional hypercube $Q_3$ is a counterexample,
with $n = 8$, $m = 12$ and $\gamma_c = 4$, so the asserted bound reads
$12 \le (8-4)^2/4 + 8 - 1 = 11$. The gap in the paper's proof (p. 143) is the
unjustified assertion that there is an edge $uv$ with
$\gamma_c(G) \le \gamma_c(G - \{u, v\})$: in $Q_3$, removing any adjacent pair
of vertices leaves a graph with connected domination number $2 < 4$.

The corollaries of the paper (Corollary 2.2 and 2.3, on leaf numbers of
triangle-free graphs) remain true; Corollary 2.2 is Graffiti.pc Conjecture 1.1,
recorded as `WrittenOnTheWallII.GraphConjecture2.conjecture2`.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/henrykmichalewski/formal-conjectures/blob/238fcea04077aee1d63c9201aa4b4b794f3a674d/FormalConjectures/Paper/SizeOrderConnectedDomination.lean#L156"]
theorem mukwembi_theorem_2_1 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj],
      G.Connected → G.CliqueFree 3 →
      (G.edgeFinset.card : ℝ) ≤
        ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4
          + (Fintype.card α : ℝ) - 1 := by
  sorry

end SizeOrderConnectedDomination
