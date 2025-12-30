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

import FormalConjectures.Util.ProblemImports

namespace Arxiv.«2107.00295»

/-!
# Conjecture 1.6

*Reference:* [arxiv/2107.00295](https://arxiv.org/abs/2107.00295)
**On independent domination of regular graphs**
by *Eun-Kyung Cho, Ilkyoo Choi, Boram Park*
-/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/--
**Conjecture 1.6 (Even case).**
For a nonempty isolate-free graph $G$ on $n$ vertices,
if $D$ is even, then $(D + 2)^2 \cdot i(G) \leq (D^2 + 4) \cdot n$.
-/
@[category research open, AMS 5]
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
-/
@[category research open, AMS 5]
theorem independentDominationOdd (hIso : 0 < G.minDegree) (hOdd : Odd G.maxDegree) :
    let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 1) * (D + 3) * i ≤ (D^2 + 3) * n := by
  sorry

end Arxiv.«2107.00295»
