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
# Erdős Problem 1067

*References:*
- [erdosproblems.com/1067](https://www.erdosproblems.com/1067)
- [BoPi24] N. Bowler and M. Pitz, A note on uncountably chromatic graphs. arXiv:2402.05984 (2024).
- [ErHa66] Erdős, P. and Hajnal, A., On chromatic number of graphs and set-systems. Acta Math. Acad.
  Sci. Hungar. (1966), 61-99.
- [Ko13] Komjáth, Péter, A note on chromatic number and connectivity of infinite graphs. Israel
  J. Math. (2013), 499--506.
- [So15] Soukup, Dániel T., Trees, ladders and graphs. J. Combin. Theory Ser. B (2015), 96--116.
- [Th17] Thomassen, Carsten, Infinitely connected subgraphs in graphs of uncountable chromatic
  number. Combinatorica (2017), 785--793.
-/

open Cardinal List

namespace Erdos1067

/--
Two walks are internally disjoint if they share no vertices other than their endpoints.
-/
def InternallyDisjoint {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

/--
We say a graph is infinitely connected if any two vertices are connected by infinitely many
pairwise disjoint paths.
-/
def InfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  Pairwise fun u v ↦ ∃ P : Set (G.Walk u v),
    P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/--
Does every graph with chromatic number $\aleph_1$ contain an infinitely connected subgraph with
chromatic number $\aleph_1$?

The answer is no, as shown by Soukup [So15](https://arxiv.org/abs/1506.00940) and Bowler and Pitz
[BoPi24](https://arxiv.org/abs/2006.04652).
-/
@[category research solved, AMS 5]
theorem erdos_1067 :
    False ↔ ∀ (V : Type) (G : SimpleGraph V), G.chromaticNumber = aleph 1 →
      ∃ (H : G.Subgraph), H.coe.chromaticNumber = aleph 1 ∧ InfinitelyConnected H.coe := by
  sorry

/--
In [ErHa66] Erdős and Hajnal asked the same question under the additional assumption that the graph
has $\aleph_1$ many vertices. Komjáth [Ko13](https://doi.org/10.1007/s11856-013-0002-6) proved that
the answer is independent of ZFC.
-/
@[category research solved, AMS 5]
theorem erdos_1067.variant.aleph_1_vertices :
    False ↔ ∀ (V : Type) (G : SimpleGraph V), #V = aleph 1 → G.chromaticNumber = aleph 1 →
      ∃ (H : G.Subgraph), H.coe.chromaticNumber = aleph 1 ∧ InfinitelyConnected H.coe := by
  sorry

end Erdos1067
