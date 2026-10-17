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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1006

*References:*
- [erdosproblems.com/1006](https://www.erdosproblems.com/1006)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er76b] Erdős, P., *Problems and results in graph theory and combinatorial analysis*.
  Proceedings of the Fifth British Combinatorial Conference (Univ. Aberdeen, Aberdeen, 1975)
  (1976), 169-192.
- [NeRo78b] Nešetřil, Jaroslav and Rödl, Vojtěch, *On a probabilistic graph-theoretical method*.
  Proc. Amer. Math. Soc. (1978), 417-421.
-/

@[expose] public section

open SimpleGraph

namespace Erdos1006

variable {V : Type*}

/-- A digraph is acyclic if it has no directed cycle, i.e. no vertex reaches itself by a
directed walk of positive length. -/
def IsAcyclic (D : Digraph V) : Prop := ∀ v, ¬ Relation.TransGen D.Adj v v

/-- The digraph obtained from `D` by reversing the direction of the arc `a → b`. -/
def reverseArc (D : Digraph V) (a b : V) : Digraph V where
  Adj x y := (D.Adj x y ∧ ¬ (x = a ∧ y = b)) ∨ (x = b ∧ y = a)

/--
Let $G$ be a graph with girth $>4$ (that is, it contains no cycles of length $3$ or $4$). Can the
edges of $G$ always be directed such that there is no directed cycle, and reversing the direction
of any edge also creates no directed cycle?

In [Er71] Erdős credits this problem to Ore, who gave an example of a graph without this property
which has girth $4$. Gallai noted that the Grötzsch graph also lacks this property.

This is false - Nešetřil and Rödl [NeRo78b] proved that, for every integer $g$, there is a graph
$G$ with girth $g$ such that every orientation of the edges in $G$ contains a directed cycle or a
cycle obtained from a directed cycle by reversing one directed edge.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1006.lean#L57"]
theorem erdos_1006 : answer(False) ↔ ∀ (V : Type) (G : SimpleGraph V), 4 < G.egirth →
    ∃ D : Digraph V, D.IsOrientation G ∧ IsAcyclic D ∧
      ∀ a b, D.Adj a b → IsAcyclic (reverseArc D a b) := by
  sorry

/--
Nešetřil and Rödl [NeRo78b] proved that, for every integer $g$, there is a graph $G$ with girth
$g$ such that every orientation of the edges in $G$ contains a directed cycle or a cycle obtained
from a directed cycle by reversing one directed edge.
-/
@[category research solved, AMS 5]
theorem erdos_1006.variants.nesetril_rodl : ∀ g : ℕ, 3 ≤ g →
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.egirth = g ∧
      ∀ D : Digraph (Fin n), D.IsOrientation G →
        ¬ IsAcyclic D ∨ ∃ a b, D.Adj a b ∧ ¬ IsAcyclic (reverseArc D a b) := by
  sorry

end Erdos1006
