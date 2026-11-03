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
# Written on the Wall II - Conjecture 372

*References:*
* [E. DeLaViña, Written on the Wall II, Conjecture 372](http://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
* [J. J. Gebendorfer, Total domination and vertex covers of trees covered by two paths](https://doi.org/10.13140/RG.2.2.25035.55849)

The source ratio uses the total domination number, the minimum vertex cover
cardinality, and the minimum number of pairwise vertex-disjoint paths covering
all vertices. Singleton paths are allowed. The ratio is restricted to path
cover number at least two; it is undefined on paths. The last declaration is
a separate, everywhere-defined formulation for trees of order at least two.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture372

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α)

/--
WOWII Conjecture 372 on its positive-denominator domain. If $T$ is a tree with
more than two vertices and path cover number $p(T) \ge 2$, then
$\gamma_t(T) \ge \tau(T)/(p(T)-1)$, where $\gamma_t$ is the total domination
number and $\tau$ is the vertex cover number.
-/
@[category research open, AMS 5]
theorem conjecture372 (hT : T.IsTree) (hn : 2 < Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    (T.vertexCoverNum.toNat : ℝ) / ((T.pathCoverNumber : ℝ) - 1) ≤
      T.totalDominationNumber := by
  sorry

/--
The two-path variant: a tree $T$ of order at least two with $p(T) \le 2$
satisfies $\tau(T) \le \gamma_t(T)$.
-/
@[category research open, AMS 5]
theorem conjecture372.variants.two_paths (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  sorry

/--
A separate formulation with no division: every tree $T$ of order at least two
satisfies $\tau(T) \le \gamma_t(T)\max\{1,p(T)-1\}$. On paths the factor is one.
-/
@[category research open, AMS 5]
theorem conjecture372.variants.regularized (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) := by
  sorry

end WrittenOnTheWallII.GraphConjecture372
