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
# TxGraffiti Conjecture 3: independent domination versus saturation (regular)

*Reference:* [arxiv/2507.17780](https://arxiv.org/abs/2507.17780)
**In Reverie Together: Ten Years of Mathematical Discovery with a Machine
Collaborator** by *Randy Davila, Boris Brimkov, Ryan Pepper*

Conjecture 3 (open since 2020) asserts that for every $r$-regular graph $G$
(every vertex has degree $r$),
$$i(G) \le \mu^*(G),$$
where $i(G)$ is the independent domination number and $\mu^*(G)$ the saturation
number (minimum size of a maximal matching).
-/

open SimpleGraph

namespace Arxiv.«2507.17780»

/--
TxGraffiti [Conjecture 3](https://arxiv.org/abs/2507.17780):
for every $r$-regular graph $G$ ($r \ge 1$),
$$i(G) \le \mu^*(G).$$

This conjecture is **open**.
-/
@[category research open, AMS 5]
theorem tx_graffiti_conjecture_3 (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (_hReg : ∀ v, G.degree v = r) (_hr : 1 ≤ r) :
    G.indepDominationNumber ≤ G.saturationNumber := by
  sorry

end Arxiv.«2507.17780»
