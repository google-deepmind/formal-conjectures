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
# Erdős Problem 718

*References:*
- [erdosproblems.com/718](https://www.erdosproblems.com/718)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25-42.
- [Di60] Dirac, Gabriel Andrew, _In abstrakten Graphen vorhandene vollständige 4-Graphen und ihre
  Unterteilungen_. Math. Nachr. (1960), 61-85.
- [Ma67] Mader, W., _Homomorphieeigenschaften und mittlere Kantendichte von Graphen_. Math. Ann.
  (1967), 265-268.
- [KoSz96] Komlós, János and Szemerédi, Endre, _Topological cliques in graphs. II_. Combin.
  Probab. Comput. (1996), 79-90.
- [BoTh96] Bollobás, Béla and Thomason, Andrew, _Highly linked graphs_. Combinatorica (1996),
  313-320.
-/

@[expose] public section

open SimpleGraph

namespace Erdos718

/-- The interior vertices of a walk from `u` to `v`: its support with the endpoints removed. -/
def walkInterior {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/-- `G` contains a subdivision of `K_r`: there are `r` distinct branch vertices and, for each
pair of them, a path in `G` joining them, such that the interiors of these paths are pairwise
disjoint and avoid the branch vertices. -/
def ContainsSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ (b : Fin r ↪ V) (p : ∀ e : {e : Fin r × Fin r // e.1 < e.2}, G.Walk (b e.1.1) (b e.1.2)),
    (∀ e, (p e).IsPath) ∧ (∀ e, Disjoint (walkInterior (p e)) (Set.range b)) ∧
      Pairwise fun e f ↦ Disjoint (walkInterior (p e)) (walkInterior (p f))

/--
Is there some constant $C>0$ such that any graph on $n$ vertices with $\geq Cr^2n$ edges contains
a subdivision of $K_r$?

A conjecture of Erdős, Hajnal, and Mader. Mader [Ma67] proved that $\geq 2^{\binom{r}{2}}n$
edges suffices. The answer is yes, proved independently by Komlós and Szemerédi [KoSz96] and
Bollobás and Thomason [BoTh96].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos718.lean#L92"]
theorem erdos_718 : answer(True) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      C * (r : ℝ) ^ 2 * Fintype.card V ≤ G.edgeSet.ncard → ContainsSubdivision G r := by
  sorry

/-- Dirac [Di60] proved that every graph on $n$ vertices with at least $2n-2$ edges contains a
subdivision of $K_4$. -/
@[category research solved, AMS 5]
theorem erdos_718.variants.dirac (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (h : 2 * Fintype.card V - 2 ≤ G.edgeSet.ncard) : ContainsSubdivision G 4 := by
  sorry

/-- Dirac [Di60] conjectured that $3n-5$ edges forces a subdivision of $K_5$. -/
@[category research open, AMS 5]
theorem erdos_718.variants.dirac_conjecture : answer(sorry) ↔
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      3 * Fintype.card V - 5 ≤ G.edgeSet.ncard → ContainsSubdivision G 5 := by
  sorry

end Erdos718
