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
# Erdős Problem 1019

*References:*
- [erdosproblems.com/1019](https://www.erdosproblems.com/1019)
- [Er69c] Erdős, P., *Über die in Graphen enthaltenen saturierten planaren Graphen*.
  Math. Nachr. (1969), 13--17.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open SimpleGraph

namespace SimpleGraph

/--
`ContainsSubdivision H G` means `G` contains a subdivision of `H`: the vertices of `H` inject into
those of `G`, and each edge of `H` is realized by a path whose internal vertices avoid the image of
that injection and are pairwise disjoint across distinct undirected edges.

Mathlib has no graph-minor or subdivision API. This is the usual topological-minor formulation of
Kuratowski's criterion.
-/
def ContainsSubdivision {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ (f : α ↪ β) (P : ∀ (x y : α), H.Adj x y → G.Walk (f x) (f y)),
    (∀ {x y : α} (h : H.Adj x y), (P x y h).IsPath) ∧
    (∀ {x y : α} (h : H.Adj x y) (a : α), f a ∉ (P x y h).support.tail.dropLast) ∧
    (∀ {x y x' y' : α} (h : H.Adj x y) (h' : H.Adj x' y'),
      s(x, y) ≠ s(x', y') →
        ∀ v ∈ (P x y h).support.tail.dropLast, v ∉ (P x' y' h').support.tail.dropLast)

/--
A simple graph is planar iff it contains no subdivision of `K₅` or `K_{3,3}` (Kuratowski).
-/
def Planar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ContainsSubdivision (completeGraph (Fin 5)) G ∧
    ¬ ContainsSubdivision (completeBipartiteGraph (Fin 3) (Fin 3)) G

/--
A planar graph on `n ≥ 3` vertices with `3n - 6` edges (the maximum possible) is called
**saturated**.
-/
def IsSaturatedPlanar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.Planar ∧ 3 ≤ Fintype.card V ∧ G.edgeSet.ncard = 3 * Fintype.card V - 6

/--
`G` contains a saturated planar subgraph on `m` vertices: some graph on `Fin m` that is saturated
planar and occurs as a (not necessarily induced) subgraph of `G`.
-/
def ContainsSaturatedPlanar {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ H : SimpleGraph (Fin m), H.IsSaturatedPlanar ∧ H.IsContained G

end SimpleGraph

namespace Erdos1019

/--
The join `G + H` of two graphs: the disjoint union together with every edge between the two parts.
-/
def graphJoin {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α ⊕ β) :=
  fromRel fun (x y : α ⊕ β) =>
    match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inr a, .inr b => H.Adj a b
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True

/--
$C_l + 2K_1$, the join of an $l$-cycle with an independent set of two vertices.
-/
def cycleJoinTwoIndep (l : ℕ) : SimpleGraph (Fin l ⊕ Fin 2) :=
  graphJoin (cycleGraph l) (⊥ : SimpleGraph (Fin 2))

/--
A planar graph on $n$ vertices with $3n-6$ edges (the maximum possible) is called saturated.
Does every graph on $n$ vertices with
$$\lfloor n^2/4\rfloor+\lfloor \frac{n+1}{2}\rfloor$$
edges contain a saturated planar subgraph with $>3$ vertices?

A saturated planar graph on $3$ vertices is a triangle, which by Turán's theorem is contained in
every graph on $n$ vertices with $\lfloor n^2/4\rfloor+1$ edges.

This was proved in the affirmative by Simonovits in his PhD thesis.
-/
@[category research solved, AMS 5]
theorem erdos_1019 : answer(True) ↔
    ∀ n ≥ 1, ∀ G : SimpleGraph (Fin n),
      n ^ 2 / 4 + (n + 1) / 2 ≤ G.edgeSet.ncard →
        ∃ m > 3, G.ContainsSaturatedPlanar m := by
  sorry

/--
Erdős [Er71] writes it is 'easy to construct' a graph on $n$ vertices with
$$\lfloor n^2/4\rfloor+\lfloor\frac{n-1}{2}\rfloor$$
edges which contains no saturated planar subgraph with $>3$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_1019.variants.construction :
    ∀ n ≥ 1, ∃ G : SimpleGraph (Fin n),
      G.edgeSet.ncard = n ^ 2 / 4 + (n - 1) / 2 ∧
        ∀ m > 3, ¬ G.ContainsSaturatedPlanar m := by
  sorry

/--
Erdős [Er69c] proved that every graph with $n$ vertices and $\lfloor n^2/4\rfloor+k$ edges contains
a saturated planar subgraph on $\gg k/n$ vertices, answering a question of Dirac.
-/
@[category research solved, AMS 5]
theorem erdos_1019.variants.dirac :
    ∃ c : ℝ, 0 < c ∧ ∀ n ≥ 1, ∀ k ≥ 1, ∀ G : SimpleGraph (Fin n),
      n ^ 2 / 4 + k ≤ G.edgeSet.ncard →
        ∃ m : ℕ, c * (k : ℝ) / n ≤ (m : ℝ) ∧ G.ContainsSaturatedPlanar m := by
  sorry

/--
Simonovits proved a strengthening: such a graph must contain either a $K_4$ or $C_l + 2K_1$ for
some $l\geq 3$. Both are saturated planar graphs on more than three vertices.
-/
@[category research solved, AMS 5]
theorem erdos_1019.variants.simonovits :
    ∀ n ≥ 1, ∀ G : SimpleGraph (Fin n),
      n ^ 2 / 4 + (n + 1) / 2 ≤ G.edgeSet.ncard →
        (completeGraph (Fin 4)).IsContained G ∨
          ∃ l ≥ 3, (cycleJoinTwoIndep l).IsContained G := by
  sorry

end Erdos1019
