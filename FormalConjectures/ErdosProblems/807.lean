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
# Erdős Problem 807

*References:*
- [erdosproblems.com/807](https://www.erdosproblems.com/807)
- [KRW88] Kratzke, Thomas and Reznick, Bruce and West, Douglas, _Eigensharp graphs:
  decomposition into complete bipartite subgraphs_. Trans. Amer. Math. Soc. (1988), 637-653.
- [Al15] Alon, Noga, _Bipartite decomposition of random graphs_. J. Combin. Theory Ser. B (2015),
  220-235.
- [ABH17] Alon, Noga and Bohman, Tom and Huang, Hao, _More on the bipartite decomposition of
  random graphs_. J. Graph Theory (2017), 45-52.
-/

@[expose] public section

open Filter Real SimpleGraph

namespace Erdos807

variable {V : Type*}

/-- A complete bipartite subgraph of `G`, given by its two disjoint parts. -/
structure Biclique (G : SimpleGraph V) where
  /-- One part of the biclique. -/
  left : Finset V
  /-- The other part of the biclique. -/
  right : Finset V
  disjoint : Disjoint left right
  complete : ∀ u ∈ left, ∀ v ∈ right, G.Adj u v

/-- The edges of a biclique. -/
def Biclique.edgeSet {G : SimpleGraph V} (B : Biclique G) : Set (Sym2 V) :=
  {e | ∃ u ∈ B.left, ∃ v ∈ B.right, e = s(u, v)}

/-- The bipartition number $\tau(G)$ of a graph $G$: the smallest number of pairwise edge
disjoint complete bipartite subgraphs whose union is $G$. -/
noncomputable def bipartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ B : Fin k → Biclique G,
    (Pairwise fun i j ↦ Disjoint (B i).edgeSet (B j).edgeSet) ∧ ⋃ i, (B i).edgeSet = G.edgeSet}

open scoped Classical in
/-- A sequence of properties of graphs holds *almost surely* for the random graph
$G(n, 1/2)$ if the proportion of labelled graphs on `n` vertices satisfying it tends to `1`. -/
def AlmostSurely (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n ↦ ((Finset.univ.filter (P n)).card : ℝ) / 2 ^ n.choose 2) atTop (nhds 1)

/--
The bipartition number $\tau(G)$ of a graph $G$ is the smallest number of pairwise edge
disjoint complete bipartite graphs whose union is $G$. The independence number $\alpha(G)$ is
the size of the largest independent subset of $G$.

Is it true that, if $G$ is a random graph on $n$ vertices with edge probability $1/2$, then
$$\tau(G)=n-\alpha(G)$$
almost surely?

Alon [Al15] showed this is false: in fact almost surely $\tau(G) \leq n-\alpha(G)-1$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos807.lean#L154"]
theorem erdos_807 : answer(False) ↔
    AlmostSurely fun n G ↦ bipartitionNumber G = n - G.indepNum := by
  sorry

/-- Alon, Bohman, and Huang [ABH17] proved that there is some absolute constant $c>0$ such
that almost surely $\tau(G) \leq n-(1+c)\alpha(G)$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos807.lean#L143"]
theorem erdos_807.variants.alon_bohman_huang :
    ∃ c : ℝ, 0 < c ∧ AlmostSurely fun n G ↦
      (bipartitionNumber G : ℝ) ≤ n - (1 + c) * G.indepNum := by
  sorry

end Erdos807
