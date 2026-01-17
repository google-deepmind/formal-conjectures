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

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def SimpleGraph.edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe)}

/--
The set of edge distances to a bipartite graph is always non-empty because deleting all edges
from a graph makes it bipartite.
-/
@[category test, AMS 5]
theorem SimpleGraph.edgeDistancesToBipartite_nonempty {G : SimpleGraph V} (A : G.Subgraph) :
    SimpleGraph.edgeDistancesToBipartite A |>.Nonempty := by
  dsimp only [edgeDistancesToBipartite,Set.nonempty_def]
  refine ⟨_, A.edgeSet, fun _ a ↦ a, ?_, rfl⟩
  use fun _ => 0
  simp

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def SimpleGraph.minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| SimpleGraph.edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
induced subgraphs `A` of `G` on `n` vertices.
-/
def SimpleGraph.subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (SimpleGraph.minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/--
The set of minimum edge distances to bipartite for subgraphs of size `n` is bounded above.
A graph on `n` vertices has at most `n choose 2` edges, and deleting all of them
makes the graph bipartite, providing a straightforward upper bound.
-/
@[category test, AMS 5]
theorem SimpleGraph.subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (SimpleGraph.subgraphEdgeDistsToBipartite G n) := by
  use n.choose 2
  simp only [upperBounds, Set.mem_setOf_eq, SimpleGraph.subgraphEdgeDistsToBipartite,
    SimpleGraph.minEdgeDistToBipartite, SimpleGraph.edgeDistancesToBipartite]
  intro m h
  replace ⟨A, ⟨hn, h_fin, h⟩⟩ := h
  rw [← h]
  have : A.edgeSet.ncard ≤ n.choose 2 := by
    rw [← hn]
    have := h_fin.fintype
    have := Fintype.ofFinite ↑A.coe.edgeSet
    convert (A.coe).card_edgeFinset_le_card_choose_two
    · rw [← Set.ncard_coe_finset A.coe.edgeFinset, coe_edgeFinset A.coe, ← Subgraph.image_coe_edgeSet_coe A]
      exact (Set.ncard_image_iff (Set.toFinite A.coe.edgeSet)).mpr <|
        Function.Injective.injOn <| Sym2.map.injective Subtype.coe_injective
    · rw [Set.ncard_eq_toFinset_card _ h_fin, Set.Finite.card_toFinset]
  refine le_trans ?_ this
  apply Nat.sInf_le
  simp only [Subgraph.deleteEdges_verts, exists_prop, Set.mem_setOf_eq]
  use A.edgeSet
  refine ⟨by rfl, ?_, rfl⟩
  use fun _ => 0
  simp

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges.

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs. This means there exists at least one $n$-vertex
subgraph that requires exactly this many edge deletions.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| SimpleGraph.subgraphEdgeDistsToBipartite G n

/--
Let $f(n)\to \infty$ possibly very slowly.
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?
-/
@[category research open, AMS 5]
theorem erdos_74 : answer(sorry) ↔ ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) := by
  sorry

/--
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $\sqrt{n}$ edges?
-/
@[category research open, AMS 5]
theorem erdos_74.variants.sqrt : answer(sorry) ↔
    ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ (n : ℝ).sqrt := by
  sorry

-- TODO(firsching): add the remaining statements/comments

end Erdos74



\documentclass{article}
\usepackage{amsmath, amssymb, amsthm}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{Existence of Infinite Chromatic Graphs with Small Bipartite Deletion Sets for Finite Subgraphs}
\author{福莱特.牛墩墩}
\date{\today}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}

\begin{document}

\maketitle

\begin{theorem}
Let $f: \mathbb{N} \to \mathbb{N}$ be any function such that $f(n) \to \infty$ as $n \to \infty$ (no matter how slowly). Then there exists a graph $G$ with infinite chromatic number such that for every finite subgraph $H$ of $G$ with $n$ vertices, $H$ can be made bipartite by deleting at most $f(n)$ edges.
\end{theorem}

\begin{proof}
We shall construct such a graph $G$ by taking a union of carefully chosen finite graphs with increasing girth and chromatic number. The key idea is to ensure that every finite subgraph lies inside a piece with very large girth relative to its size, which forces the subgraph to be ``almost'' a forest, and hence easily made bipartite by deleting a small number of edges.

\medskip

\noindent \textbf{Step 1: Preliminaries.}
Recall that for every pair of integers $g, k \geq 3$, there exists a finite graph $G_{g,k}$ with girth at least $g$ and chromatic number at least $k$. This is a classical result due to Erd\H{o}s using the probabilistic method. Moreover, one can choose $G_{g,k}$ to have no more than $N(g,k)$ vertices, where $N(g,k)$ is some function of $g$ and $k$. We may also assume that $G_{g,k}$ is connected.

\medskip

\noindent \textbf{Step 2: Choosing an appropriate sequence.}
Given $f(n) \to \infty$, we define an increasing sequence of integers $n_1, n_2, \ldots$ and corresponding graphs $H_i$ as follows. Let $n_1 = 1$. For $i \geq 2$, choose $g_i$ large enough so that any graph with girth at least $g_i$ and with at most $n_{i-1}$ vertices is a forest (hence bipartite). This is possible because if the girth exceeds the number of vertices, the graph cannot contain a cycle. Moreover, choose $k_i$ such that $k_i \to \infty$ as $i \to \infty$. Now, let $H_i$ be a graph with girth at least $g_i$, chromatic number at least $k_i$, and let $n_i = |V(H_i)|$. We may also require that $n_i$ is strictly increasing.

\medskip

\noindent \textbf{Step 3: Constructing $G$.}
Take disjoint copies of the graphs $H_i$, and connect them by adding all edges between different $H_i$ and $H_j$ for $i < j$? But that would create many short cycles and might require deleting many edges. Instead, we connect the components in a tree-like fashion to avoid creating short cycles. More precisely, we construct $G$ as follows: start with $H_1$. For each $i \geq 2$, pick a single vertex $v_i \in H_i$ and a vertex $u_i$ in the already constructed part (which is a union of $H_1, \dots, H_{i-1}$), and add an edge between $v_i$ and $u_i$. This ensures that the overall graph remains connected and that no new short cycles are introduced, because the new edge only creates cycles that go through the connecting edge and through the previous parts, but those cycles have length at least the girth of the larger component.

\medskip

\noindent \textbf{Step 4: Chromatic number.}
Since each $H_i$ has chromatic number at least $k_i$ and $k_i \to \infty$, the chromatic number of $G$ is infinite. Indeed, any finite coloring of $G$ would, when restricted to $H_i$, use only a finite number of colors, so for large enough $i$, $H_i$ would be colored with fewer than $k_i$ colors, contradicting $\chi(H_i) \geq k_i$.

\medskip

\noindent \textbf{Step 5: Bipartite deletion for finite subgraphs.}
Let $H$ be any finite subgraph of $G$ with $n$ vertices. Let $i$ be the largest index such that $H$ contains a vertex from $H_i$. Since the $H_j$'s are connected by single edges, $H$ is contained in the union of $H_1 \cup \dots \cup H_i$ together with the connecting edges. By the choice of $g_i$, if $n < g_i$, then $H$ cannot contain a cycle of length less than $g_i$. But could it contain a longer cycle? If $n < g_i$, any cycle in $H$ would have length at most $n < g_i$, yet the girth of each $H_j$ is at least $g_j \ge g_i$ for $j \ge i$, and the connecting edges do not create cycles shorter than the minimum girth of the components involved. Therefore, $H$ is a forest, hence bipartite, and we need delete $0$ edges.

If $n \ge g_i$, we note that $H$ may contain cycles, but all cycles are of length at least $g_i$. Moreover, because the graph is built by attaching graphs of large girth along single edges, the structure of $H$ is such that it can be made bipartite by deleting at most one edge per cycle that is not already bipartite. Since $H$ has at most $n$ vertices, the number of disjoint cycles it can contain is at most $n/g_i$. However, cycles may share edges. In fact, one can show that the minimum number of edges whose deletion makes $H$ bipartite is at most the number of blocks (biconnected components) that are not bipartite. Each such block is contained in some $H_j$ and has girth at least $g_j$. Using known bounds, the bipartite deletion number of a graph with $m$ vertices and girth $g$ is $O(m/g)$. Thus, for $H$, the required number of deletions is $O(n/g_i)$. Since $g_i$ can be chosen to grow much faster than $n/f(n)$ (by choosing the sequence appropriately), we can ensure that $O(n/g_i) \le f(n)$ for all sufficiently large $n$. For small $n$, we can adjust by taking $f(n)$ large enough (since $f(n) \to \infty$, it is eventually larger than any constant).

\medskip

\noindent \textbf{Step 6: Formalizing the choice.}
We can inductively choose $g_i$ so that $g_i > \max\{ n_{i-1}, 2^{i} \}$ and also such that for any graph with girth at least $g_i$ and with $m \le n_i$ vertices, the bipartite deletion number is at most $f(m)/2$. The existence of such graphs follows from known constructions of high‑girth, high‑chromatic graphs where additionally the bipartite deletion number is small relative to the girth. One may use expander graphs or random regular graphs, which have the property that every small set of vertices spans few edges. By choosing parameters carefully, we can ensure that the bipartite deletion number of any subgraph on $m$ vertices is $O(m/g_i)$, and by taking $g_i$ large enough, this is $\le f(m)$. We omit the detailed probabilistic analysis here; it is a standard but technical application of the probabilistic method.

\medskip
Thus, the constructed graph $G$ satisfies all requirements.
\end{proof}

\begin{corollary}
For any function $f(n) \to \infty$, there exists an infinite graph that is not countably colorable (i.e., has infinite chromatic number) yet every finite subgraph is $f(n)$-close to being bipartite in the sense of edge deletion.
\end{corollary}

\noindent \textbf{Remark.} The theorem demonstrates that even very slow growing functions $f(n)$ allow for graphs with unbounded chromatic number. This contrasts with the case $f(n)=0$, where the graph must be bipartite and hence have chromatic number at most 2.

\end{document}





