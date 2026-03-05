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
# Erdős Problem 559

*Reference:* [erdosproblems.com/559](https://www.erdosproblems.com/559)

Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such
that there is a graph $H$ with $m$ edges that is Ramsey for $G$ (every 2-coloring
of the edges of $H$ contains a monochromatic copy of $G$).

The conjecture: if $G$ has $n$ vertices and maximum degree $d$ then $\hat{R}(G) \ll_d n$
(i.e., $\hat{R}(G) \leq C_d \cdot n$ for some constant $C_d$ depending only on $d$).

This was disproved by Rödl and Szemerédi [RoSz00] for $d = 3$, who
constructed graphs on $n$ vertices with maximum degree 3 such that
$\hat{R}(G) \gg n (\log n)^c$ for some absolute constant $c > 0$.

[RoSz00] Rödl, V. and Szemerédi, E., _On size Ramsey numbers of graphs with bounded degree_. Combinatorica 20 (2000), 257-262.
-/

open SimpleGraph

namespace Erdos559

/-- The size Ramsey number $\hat{R}(G)$: the minimum number of edges in a graph $H$
    that is Ramsey for $G$.

    A graph $H$ on $N$ vertices is Ramsey for $G$ if every 2-coloring of the edges
    of $H$ (represented as a symmetric function $c : \text{Fin}\ N \to \text{Fin}\ N \to \text{Bool}$)
    contains a monochromatic copy of $G$, i.e., an injective map $f$ from the
    vertices of $G$ into $\text{Fin}\ N$ that preserves adjacency in $H$ and maps all
    edges to the same color. -/
noncomputable def sizeRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ (N : ℕ) (H : SimpleGraph (Fin N)),
    Nat.card H.edgeSet = m ∧
    ∀ (c : Fin N → Fin N → Bool),
      (∀ i j, c i j = c j i) →
      ∃ (b : Bool) (f : V → Fin N),
        Function.Injective f ∧
        (∀ u v, G.Adj u v → H.Adj (f u) (f v)) ∧
        (∀ u v, G.Adj u v → c (f u) (f v) = b)}

/--
Erdős Problem 559 (DISPROVED) [RoSz00]:

The original conjecture states: for every $d \geq 1$, there exists a constant $C$
(depending only on $d$) such that for all $n \geq 1$ and all graphs $G$ on $n$ vertices
with maximum degree at most $d$, the size Ramsey number satisfies $\hat{R}(G) \leq C \cdot n$.

This was disproved by Rödl and Szemerédi [RoSz00] for $d = 3$.
-/
@[category research solved, AMS 5]
theorem erdos_559 :
    answer(False) ↔ (∀ d : ℕ, d ≥ 1 →
      ∃ C : ℕ, ∀ n : ℕ, n ≥ 1 →
        ∀ G : SimpleGraph (Fin n),
          (∀ v, Nat.card (G.neighborSet v) ≤ d) →
            sizeRamseyNumber G ≤ C * n) := by
  sorry

end Erdos559
