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
# Erdős Problem 1009

*References:*
- [erdosproblems.com/1009](https://www.erdosproblems.com/1009)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97--109.
- [Gy88] Győri, E., *On the number of edge-disjoint triangles in graphs of given size*. (1988),
  267--276.
-/

@[expose] public section

namespace Erdos1009

/--
Is it true that, for every $c>0$, there exists $f(c)$ such that every graph on $n$ vertices with
at least $\lfloor n^2/4\rfloor+k$ edges, where $k<c n$, contains at least $k-f(c)$ many edge
disjoint triangles?

Erdős [Er71] proved this for $c<1/2$ using a theorem of Erdős and Gallai, which says that every
graph on $n$ vertices with at least $(n-1)^2/4+2$ many edges, with chromatic number $3$, must
contain a triangle. In fact, Erdős proved this is true with $f(c)=0$ for $c<1/2$. At first Erdős
thought $f(c)=0$ for larger values of $c$ but this is false: an example of Sauer proves that
$f(2)\geq 1$.

This is true, and was proved by Győri [Gy88] who proved that this is true with $f(c)\ll c^2$,
and also that $f(c)=0$ if $c<2$ for odd $n$ or $c<3/2$ for even $n$.

A family of edge disjoint triangles is a finite set of $3$-cliques of $G$ any two of which share
at most one vertex.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1009.lean#L2347"]
theorem erdos_1009 : answer(True) ↔ ∀ c : ℝ, 0 < c → ∃ f : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    n ^ 2 / 4 + k ≤ G.edgeSet.ncard → (k : ℝ) < c * n →
      ∃ T : Finset (Finset (Fin n)), (∀ t ∈ T, G.IsNClique 3 t) ∧
        (T : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ k ≤ T.card + f := by
  sorry

/--
Sauer gave an example of a graph on $n$ vertices with $\lfloor n^2/4\rfloor+2n-6$ many edges
which contains only $2n-7$ many edge disjoint triangles: if $n=2r+4$ then $G$ is the complete
tripartite graph on $[r]\times [r]\times [4]$, with a $K_4$ on the $[4]$ vertices also.
-/
@[category research solved, AMS 5]
theorem erdos_1009.variants.sauer : ∀ r : ℕ, 1 ≤ r → ∃ G : SimpleGraph (Fin (2 * r + 4)),
    G.edgeSet.ncard = (2 * r + 4) ^ 2 / 4 + 2 * (2 * r + 4) - 6 ∧
      ∀ T : Finset (Finset (Fin (2 * r + 4))), (∀ t ∈ T, G.IsNClique 3 t) →
        (T : Set (Finset (Fin (2 * r + 4)))).Pairwise (fun s t => (s ∩ t).card ≤ 1) →
          T.card ≤ 2 * (2 * r + 4) - 7 := by
  sorry

end Erdos1009
