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
# TxGraffiti Conjecture 1: independence, annihilation, and residue

*Reference:* [arxiv/2507.17780](https://arxiv.org/abs/2507.17780)
**In Reverie Together: Ten Years of Mathematical Discovery with a Machine
Collaborator** by *Randy Davila, Boris Brimkov, Ryan Pepper*

Conjecture 1, the oldest of the four TxGraffiti conjectures in the cited
collection (open since 2016), asserts that every nontrivial connected graph $G$
with maximum degree $\Delta \ge 2$ satisfies
$$\alpha(G) \ge \frac{a(G) + R(G)}{\Delta(G)},$$
where $\alpha$ is the independence number, $a$ the annihilation number, $R$ the
Havel–Hakimi residue, and $\Delta$ the maximum degree.

This conjecture is **true**, proved in
[arXiv:2606.29553](https://arxiv.org/abs/2606.29553) (C. Gupta).
-/

open SimpleGraph

namespace Arxiv.«2507.17780»

/--
TxGraffiti [Conjecture 1](https://arxiv.org/abs/2507.17780):
for every nontrivial connected graph $G$ with $\Delta(G) \ge 2$,
$$\alpha(G) \ge \frac{a(G) + R(G)}{\Delta(G)}.$$

This conjecture is **true**.

**Proof sketch.** Substitute the Caro–Wei lower bound $\alpha \ge W$ for $\alpha$
and reduce to $a \le (\Delta - 1) \alpha$. The case $\Delta = 2$ is trivial
($a = \alpha$). For $\Delta \ge 4$ an AM–HM argument with $m \le (n - a)\Delta$
yields a quadratic whose discriminant is negative. For $\Delta = 3$ the
annihilation number has a closed form in the degree counts $(n_1, n_2, n_3)$ and
$a \le 2W$ is verified in three regimes. See
[arXiv:2606.29553](https://arxiv.org/abs/2606.29553).
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/ChakshuGupta13/lab/tree/main/math/gupta2026annihilation"]
theorem tx_graffiti_conjecture_1 (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected)
    (_hDeg : 2 ≤ G.maxDegree) :
    (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum := by
  sorry

end Arxiv.«2507.17780»
