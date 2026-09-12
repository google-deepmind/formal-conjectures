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

import FormalConjecturesUtil

/-!
# Independent Domination of Regular Graphs, Conjecture 1.6

*Reference:* [arxiv/2107.00295](https://arxiv.org/abs/2107.00295)
**On independent domination of regular graphs**
by *Eun-Kyung Cho, Ilkyoo Choi, Boram Park*

The conjecture was subsequently proved by Cho, Kim, Kim and Oum, as
Corollary 1.3 of:

*Reference:* [arxiv/2202.09594](https://arxiv.org/abs/2202.09594)
**Independent domination of graphs with bounded maximum degree**
by *Eun-Kyung Cho, Jinha Kim, Minki Kim, Sang-il Oum*,
J. Combin. Theory Ser. B 158 (2023), 341-352.

Corollary 1.3 states that every graph $G$ with maximum degree at most $\Delta$
and no isolated vertices has an independent dominating set of size at most
$\left(1 - \frac{\Delta}{\lfloor (\Delta+2)^2/4 \rfloor}\right)\lvert V(G)\rvert$.
Expanding the floor for even and odd $\Delta$ gives exactly the two
statements below.
-/
namespace Arxiv.«2107.00295»
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/--
**Conjecture 1.6 (Even case).**
For a nonempty isolate-free graph $G$ on $n$ vertices,
if $D$ is even, then $(D + 2)^2 \cdot i(G) \leq (D^2 + 4) \cdot n$.

Proved by Cho, Kim, Kim and Oum ([arxiv/2202.09594](https://arxiv.org/abs/2202.09594),
Corollary 1.3).
-/
@[category research solved, AMS 5]
theorem independentDominationEven (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree) :
    let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n := by
  sorry

/--
**Conjecture 1.6 (Odd case).**
For a nonempty isolate-free graph $G$ on $n$ vertices,
if $D$ is odd, then $(D + 1)(D + 3) \cdot i(G) \leq (D^2 + 3) \cdot n$.

Proved by Cho, Kim, Kim and Oum ([arxiv/2202.09594](https://arxiv.org/abs/2202.09594),
Corollary 1.3).
-/
@[category research solved, AMS 5]
theorem independentDominationOdd (hIso : 0 < G.minDegree) (hOdd : Odd G.maxDegree) :
    let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 1) * (D + 3) * i ≤ (D^2 + 3) * n := by
  sorry

end Arxiv.«2107.00295»
