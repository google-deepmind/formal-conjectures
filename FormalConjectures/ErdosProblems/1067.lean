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

open Cardinal SimpleGraph

namespace Erdos1067

/--
A graph is infinitely edge-connected if to disconnect the graph requires deleting
infinitely many edges. In other words, removing any finite set of edges leaves
the graph connected.
-/
def InfinitelyEdgeConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.Finite → (G.deleteEdges s).Connected

/--
Does every graph with chromatic number $\aleph_1$ contain an infinitely connected subgraph with
chromatic number $\aleph_1$?

Komjáth [Ko13] proved that it is consistent that the answer is no. This was improved by
Soukup [So15], who constructed a counterexample using no extra set-theoretical assumptions. A
simpler elementary example was given by Bowler and Pitz [BoPi24].
-/
@[category research solved, AMS 5]
theorem erdos_1067 :
    answer(False) ↔ ∀ (V : Type) (G : SimpleGraph V), G.chromaticNumber = aleph 1 →
      ∃ (H : G.Subgraph), H.coe.chromaticNumber = aleph 1 ∧ InfinitelyConnected H.coe := by
  sorry

/--
Thomassen [Th17] constructed a counterexample to the version which asks for infinite
edge-connectivity (that is, to disconnect the graph requires deleting infinitely many edges).
-/
@[category research solved, AMS 5]
theorem erdos_1067.variant.infinite_edge_connectivity :
    answer(False) ↔ ∀ (V : Type) (G : SimpleGraph V), G.chromaticNumber = aleph 1 →
      ∃ (H : G.Subgraph), H.coe.chromaticNumber = aleph 1 ∧ InfinitelyEdgeConnected H.coe := by
  sorry

-- TODO: Formalize variant independent of ZFC.

end Erdos1067
