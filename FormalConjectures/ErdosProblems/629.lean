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
public import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.List

/-!
# Erdős Problem 629

*References:*
- [erdosproblems.com/629](https://www.erdosproblems.com/629)
- [ERT80] Erdős, Paul and Rubin, Arthur L. and Taylor, Herbert, *Choosability in graphs*.
  Proceedings of the West Coast Conference on Combinatorics, Graph Theory and Computing (1979),
  Congress. Numer. XXVI (1980), 125-157. [PDF](https://www.renyi.hu/~p_erdos/1980-07.pdf)
- [HMT96] Hanson, Denis and MacGillivray, Gary and Toft, Bjarne, *Choosability of bipartite
  graphs*. Ars Combin. (1996), 183-192.
- [RaSr00] Radhakrishnan, Jaikumar and Srinivasan, Aravind, *Improved bounds and algorithms for
  hypergraph $2$-coloring*. Random Structures Algorithms (2000), 4-32.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos629

/-- $n(k)$: the least number of vertices of a bipartite graph $G$ with $\chi_L(G) > k$.
Bipartite means `Colorable 2`, as in [ERT80], which asks for the least number of nodes of a
$2$-colorable graph that is not $k$-choosable. -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin m), G.Colorable 2 ∧ k < G.listChromaticNumber}

/-- Any bipartite graph $G$ on $m$ vertices with $\chi_L(G) > k$ gives $n(k) \leq m$. -/
@[category API, AMS 5]
theorem n_le {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2)
    (hk : k < G.listChromaticNumber) : n k ≤ m :=
  Nat.sInf_le ⟨G, hG, hk⟩

def erdos_629.answer : ℕ → ℕ := sorry

/--
The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any
assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different
vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent
vertices receive distinct colours.

Determine the minimal number of vertices $n(k)$ of a bipartite graph $G$ such that
$\chi_L(G)>k$.
-/
@[category research open, question value, AMS 5]
theorem erdos_629 : n = erdos_629.answer := by
  sorry

/--
A problem of Erdős, Rubin, and Taylor [ERT80], who proved that
$$2^{k-1}<n(k) <k^22^{k+2}.$$

The chain of inequalities in [ERT80, p. 129] needs $k \geq 2$, since $m(1) = 1 = 2^0$; for
$k = 1$ the claim holds because $n(1) = 2$. The case $k = 0$ is degenerate ($n(0) = 1$).
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.ert_bounds (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (k - 1) < n k ∧ n k < k ^ 2 * 2 ^ (k + 2) := by
  sorry

/--
They also prove that if $m(k)$ is the size of the smallest family of $k$-sets without property B
(i.e. the smallest number of $k$-sets in a graph with chromatic number $3$) then
$m(k)\leq n(k)\leq m(k+1)$.

[ERT80, p. 129] prints the upper bound as $2m(k)$; we state that form. Here $m(k)$ is
`Hypergraph.minChromaticEdges k 3`, as in Erdős Problem 901. We assume $k \geq 2$: for $k = 1$
this is `⊤`, since singleton edges admit no proper colouring, whereas $m(1) = 1$.
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.property_b (k : ℕ) (hk : 2 ≤ k) :
    (Hypergraph.minChromaticEdges k 3).toNat ≤ n k ∧
      n k ≤ 2 * (Hypergraph.minChromaticEdges k 3).toNat := by
  sorry

/--
The lower bounds on $m(k)$ by Radhakrishnan and Srinivasan [RaSr00] imply that
$$2^k \left(\frac{k}{\log k}\right)^{1/2}\ll n(k).$$
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.radhakrishnan_srinivasan :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      c * 2 ^ k * Real.sqrt (k / Real.log k) ≤ (n k : ℝ) := by
  sorry

/--
Erdős, Rubin, and Taylor [ERT80] proved $n(2)=6$.
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.n_two : n 2 = 6 := by
  sorry

/--
Hanson, MacGillivray, and Toft [HMT96] proved $n(3)=14$.
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.n_three : n 3 = 14 := by
  sorry

/--
Hanson, MacGillivray, and Toft [HMT96] proved
$$n(k) \leq kn(k-2)+2^k.$$
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.hmt_recursion (k : ℕ) (hk : 2 ≤ k) :
    n k ≤ k * n (k - 2) + 2 ^ k := by
  sorry

end Erdos629
