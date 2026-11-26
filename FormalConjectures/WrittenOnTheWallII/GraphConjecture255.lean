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
# Written on the Wall II - Conjecture 255

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [kiankyars/math, `OpenProblem/WOWII255.lean` (October 2026)](https://github.com/kiankyars/math/blob/44c055de24fb240a3a9d43fa562742de285bc3d5/OpenProblem/WOWII255.lean)
  gives the earliest public counterexample we know of, on eleven vertices, with a Lean proof,
  and reports that an exhaustive search finds none on at most ten vertices.
- [burgerge/wowii255-total-domination (November 2026)](https://github.com/burgerge/wowii255-total-domination/tree/8a5466568fee28639d82208e08eebab3e3751df6)
  proves in Lean that the least order of a counterexample is eleven and that the inequality
  with the constant $2$ replaced by $c$ holds for all connected graphs on at least two vertices
  exactly when $c \le 1$.
- [T. Newton, Minimum-order counterexamples to Graffiti.pc Conjecture 256 and sharp bounds for
  total domination (2026)](https://doi.org/10.5281/zenodo.24427699)
  proves the covering bound $n \le (\gamma_t(G) - 1) M(G)$ used below, for the sibling
  Conjecture 256.
- [A. Manrique de Lara Martín, Smallest counterexamples and unbounded families for Graffiti.pc
  Conjectures 108, 255, 382c and 393d (2026)](https://doi.org/10.5281/zenodo.24569378)
  classifies the counterexamples on eleven vertices and finds the best constant for each value
  of the total domination number.

The conjecture is false. Take a path $a - b - c$, four pairwise adjacent vertices
$x_1, \dots, x_4$ adjacent to $a$, four pairwise non-adjacent vertices $y_1, \dots, y_4$
adjacent to $c$, and the edges $x_i y_i$; there are no other edges. This graph has eleven
vertices. Every vertex has eccentricity two, so all eleven vertices are centers. Every edge $e$
has $|N(e)| = 7$. The set $\{a, b, c\}$ is a total dominating set, so $\gamma_t(G) \le 3$,
while the conjecture claims $\gamma_t(G) \ge 22/7$.

Write $n$ for the number of vertices, $M(G)$ for the maximum of $|N(e)|$ and $C$ for the set of
centers. A minimum total dominating set $D$ induces a graph without isolated vertices, so $D$
is covered by at most $\gamma_t(G) - 1$ edges with both ends in $D$, and every vertex lies in
$N(e)$ for one of them. Hence $|C| \le n \le (\gamma_t(G) - 1) M(G)$, so for graphs with
$\gamma_t(G) = t$ the inequality holds with the constant $2$ replaced by $t/(t-1)$. For $t = 2$
this is the conjectured constant. For $t \ge 3$ no larger constant works, so the constant $2$
fails for every $t \ge 3$.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture255

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The maximum of $|N(e)|$ over the edges $e = uv$ of $G$, where $N(e) = N(u) \cup N(v)$ is the
union of the open neighborhoods of the two ends (WOWII definition 28). Since $u$ and $v$ are
adjacent, both belong to $N(e)$, so closed neighborhoods give the same set. The value is `0`
for a graph without edges. -/
def maxEdgeNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2).sup
    fun p => (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card

/--
WOWII [Conjecture 255](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
states that every simple connected graph $G$ satisfies
$\gamma_t(G) \ge 2|C| / \max \{|N(e)| : e \text{ an edge of } G\}$,
where $C$ is the set of centers of $G$.

Here $\gamma_t(G)$ is the total domination number, a center is a vertex of minimum
eccentricity, and $N(e)$ is the union of the open neighborhoods of the two ends of $e$.
The source writes the maximum of $\{N(e)\}$; since $N(e)$ is a set, this is read as the
maximum of $|N(e)|$. The statement is restricted to graphs with at least two vertices, so that
$G$ has an edge and a total dominating set.

The conjecture is false. The earliest counterexample we know of, on eleven vertices, is in
`kiankyars/math` (October 2026).
-/
@[category research solved, AMS 5]
theorem conjecture255 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected →
        (2 * G.center.ncard : ℝ) / (maxEdgeNeighborhood G : ℝ) ≤ G.totalDominationNumber := by
  sorry

/--
The inequality of WOWII Conjecture 255 holds for every connected graph on at least two and at
most ten vertices. Together with the counterexample on eleven vertices, this shows that the
least order of a counterexample is eleven.

`kiankyars/math` reports an exhaustive computer search with this outcome.
`burgerge/wowii255-total-domination` proves the statement in Lean
(`WOWII255.bound_of_card_le_ten`), through the stronger bound $2n \le \gamma_t(G) M(G)$.
-/
@[category research solved, AMS 5]
theorem conjecture255.variants.at_most_ten_vertices [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hV : Fintype.card V ≤ 10) :
    (2 * G.center.ncard : ℝ) / (maxEdgeNeighborhood G : ℝ) ≤ G.totalDominationNumber := by
  sorry

/--
A corrected form of WOWII Conjecture 255: every connected graph $G$ on at least two vertices
satisfies $|C| \le (\gamma_t(G) - 1) \cdot \max_e |N(e)|$. Such a graph has $\gamma_t(G) \ge 2$,
so the subtraction in `ℕ` is exact. For graphs with $\gamma_t(G) = t$ this is the conjectured
inequality with the constant $2$ replaced by $t/(t-1)$.

The proof is the covering argument of T. Newton for Conjecture 256, together with
$|C| \le n$.
-/
@[category research solved, AMS 5]
theorem conjecture255.variants.fixed_total_domination [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    G.center.ncard ≤ (G.totalDominationNumber - 1) * maxEdgeNeighborhood G := by
  sorry

/--
The constant $t/(t-1)$ of `conjecture255.variants.fixed_total_domination` is best possible
for every $t \ge 2$: for every $c > t/(t-1)$ there is a connected graph $G$ with
$\gamma_t(G) = t$ and $\gamma_t(G) \cdot \max_e |N(e)| < c\,|C|$.

For $t = 2$ the graph $K_2$ works. For $t \ge 3$ the graphs $F(t-1, s)$ of A. Manrique de Lara
Martín (2026), for $s$ large, have diameter two, every vertex a center, and $\gamma_t = t$.
-/
@[category research solved, AMS 5]
theorem conjecture255.variants.fixed_total_domination_sharp
    (t : ℕ) (ht : 2 ≤ t) (c : ℝ) (hc : (t : ℝ) / ((t : ℝ) - 1) < c) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj),
      G.Connected ∧ G.totalDominationNumber = t ∧
        (t * maxEdgeNeighborhood G : ℝ) < c * G.center.ncard := by
  sorry

-- Sanity checks

/-- In the path $0 - 1 - 2$, both edges have $N(e) = \{0, 1, 2\}$. -/
@[category test, AMS 5]
example : maxEdgeNeighborhood
    (SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2)} : SimpleGraph (Fin 3)) = 3 := by
  decide

/-- In the complete graph on four vertices, every edge has $N(e)$ equal to the vertex set. -/
@[category test, AMS 5]
example : maxEdgeNeighborhood (⊤ : SimpleGraph (Fin 4)) = 4 := by
  decide

/-- A graph without edges gives the empty maximum `0`. -/
@[category test, AMS 5]
example : maxEdgeNeighborhood (⊥ : SimpleGraph (Fin 3)) = 0 := by
  decide

/-- In the counterexample on eleven vertices described above, with $a, b, c = 0, 1, 2$,
$x_i = 2 + i$ and $y_i = 6 + i$, the maximum of $|N(e)|$ is $7$. -/
@[category test, AMS 5]
example : maxEdgeNeighborhood
    (SimpleGraph.fromEdgeSet
      {s(0, 1), s(1, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6), s(2, 7), s(2, 8), s(2, 9), s(2, 10),
        s(3, 7), s(4, 8), s(5, 9), s(6, 10),
        s(3, 4), s(3, 5), s(3, 6), s(4, 5), s(4, 6), s(5, 6)} : SimpleGraph (Fin 11)) = 7 := by
  decide +kernel

end WrittenOnTheWallII.GraphConjecture255
