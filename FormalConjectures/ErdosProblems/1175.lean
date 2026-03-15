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
# Erdős Problem 1175

*Reference:* [erdosproblems.com/1175](https://www.erdosproblems.com/1175)

For an uncountable cardinal κ, must there exist a cardinal λ such that every graph with
chromatic number λ contains a triangle-free subgraph with chromatic number κ?

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999 (1999), §7.92.
-/

open Cardinal SimpleGraph

namespace Erdos1175

/--
Erdős Problem 1175 [Va99, 7.92]:

Let $\kappa$ be an uncountable cardinal. Must there exist a cardinal $\lambda$ such that
every graph with chromatic number $\lambda$ contains a triangle-free subgraph
with chromatic number $\kappa$?

Here `G.chromaticCardinal` is the minimal cardinality of a color set admitting a proper
coloring of $G$. Triangle-free means `G.CliqueFree 3` (no 3-clique, i.e., no triangle).
The subgraph relation $H \leq G$ holds when every edge of $H$ is also an edge of $G$.

Shelah proved that a negative answer is consistent if $\kappa = \lambda = \aleph_1$.
-/
@[category research open, AMS 3 5]
theorem erdos_1175 : answer(sorry) ↔
    ∀ κ : Cardinal.{0}, aleph 1 ≤ κ →
    ∃ mu : Cardinal.{0},
      ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = mu →
        ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ H.chromaticCardinal = κ := by
  sorry

end Erdos1175
