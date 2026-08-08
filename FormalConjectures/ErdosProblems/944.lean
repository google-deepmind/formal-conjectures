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

import FormalConjecturesUtil

/-!
# Erdős Problem 944

*Reference:* [erdosproblems.com/944](https://www.erdosproblems.com/944)
-/

universe u
variable {V : Type u}

namespace Erdos944

open Erdos944

/--
The predicate that graph $G$ with chromatic number $k$ is such that every vertex is critical, yet
every critical set of edges has size $>r$
-/
def SimpleGraph.IsErdos944 (G : SimpleGraph V) (k r : ℕ) : Prop :=  G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard)

/--
Let $k \ge 4$ and $r\ge 1$. Must there exist a graph $G$ with chromatic number $k$
 such that every vertex is critical, yet every critical set of edges has size $>r$?
-/
@[category research open, AMS 11]
theorem erdos_944 :
    answer(sorry) ↔ ∀ k ≥ 4, ∀ r ≥ 1, ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k r := by
  sorry

/--
Let $k \ge 4$. Must there exist a graph $G$ with chromatic number $k$
such that every vertex is critical, yet every critical set of edges has size $>1$?

This was conjectured by Dirac in 1970.
-/
@[category research open, AMS 11]
theorem erdos_944.variants.dirac_conjecture :
    answer(sorry) ↔ ∀ k ≥ 4, ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry


/--
Dirac's conjecture was proved, for $k=5$: There exists a graph $G$ with chromatic number $5$, such
that every vertex is critical, yet every critical set of edges has size $>1$, or in other words:
has no critical edge.

[Br92] Brown, Jason I., A vertex critical graph without critical edges. Discrete Math. (1992), 99--101
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_eq_5 :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 5 1 := by
  sorry

/--
Lattanzio [La02] proved there exist $k$-critical graphs without critical edges for all $k$ such that
$k - 1$ is not prime.

[La02] Lattanzio, John J., A note on a conjecture of {D}irac. Discrete Math. (2002), 323--330
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_sub_one_not_prime (k : ℕ) (hk : 4 ≤ k)
    (h : ¬ (k - 1).Prime) : ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry

/--
Jensen [Je02] gave an construction for $k$-critical graphs without any critical edges for all $k ≥ 5$.

[Je02] Jensen, Tommy R., Dense critical and vertex-critical graphs. Discrete Math. (2002), 63--84.
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_ge_five (k : ℕ) (hk : 5 ≤ k) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry

/--
The case $k=4$ and $r=1$ remains open: Are there $4$-critical graphs without any critical edges?
-/
@[category research open, AMS 11]
theorem erdos_944.variants.dirac_conjecture.k_eq_four :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 4 1 := by
  sorry

/--
Martinsson and Steiner [MaSt25] proved for every $r \ge 1$ if $k$ is sufficiently large, depending
on $r$, there exist a graph $G$ with chromatic number $k$ such that every vertex is critical,
yet every critical set of edges has size $>r$.

[MaSt25] Martinsson, Anders and Steiner, Raphael, Vertex-critical graphs far from edge-criticality. Combin. Probab. Comput. (2025), 151--157
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.large_k_for_any_r (r : ℕ) (hr : 1 ≤ r) : ∀ᶠ k in Filter.atTop,
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k r := by
  sorry

/-
## Verified partial result for the $k = 4$, $r = 1$ case (6-regular subproblem)

Skottová and Steiner [SkSt25] proved that every $(4,1)$-graph (a $4$-vertex-critical graph with
no critical edge) has minimum degree and edge-connectivity at least $6$, and asked (their
Problem 5.2) whether a $6$-regular $(4,1)$-graph exists. A verified computational programme [Fe26]
shows that there is no $6$-regular $4$-vertex-critical graph on $n \le 15$ except a unique one on
$n = 13$ (which has critical edges); hence any $6$-regular $(4,1)$-graph has at least $16$
vertices.

[SkSt25] Skottová, Ema and Steiner, Raphael, _Critical edge sets in vertex-critical graphs_,
arXiv:2508.08703 (2025).

[Fe26] Ferudun, A., _Exact $6$-cut rigidity and small-order superconnectivity for the $6$-regular
case of Dirac's $k = 4$ problem_, arXiv:2606.18462 (2026). The full proofs, code, certificates,
and Lean cores are provided there.
-/

/-- Any $6$-regular $(4,1)$-graph — a $6$-regular $4$-vertex-critical graph with no critical
edge — has at least $16$ vertices: a verified computation [Fe26] rules out every such graph on
$n \le 15$, settling the small-order cases of Skottová–Steiner Problem 5.2 [SkSt25]. -/
@[category research solved, AMS 5]
theorem erdos_944.variants.dirac_conjecture.k_eq_four.six_regular_min_order
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 6) (h : G.IsErdos944 4 1) :
    16 ≤ Fintype.card V := by
  sorry

end Erdos944
