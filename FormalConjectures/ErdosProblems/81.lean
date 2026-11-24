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
# Erdős Problem 81

*References:*
- [erdosproblems.com/81](https://www.erdosproblems.com/81)
- [EOZ93] Erdős, Paul and Ordman, Edward T. and Zalcstein, Yechezkel,
  *Clique partitions of chordal graphs*. Combin. Probab. Comput. (1993), 409–415.
- [CEO94] Chen, Guan-Tao and Erdős, Paul and Ordman, Edward T.,
  *Clique partitions of split graphs*. Combinatorics, graph theory, algorithms and applications
  (Beijing, 1993) (1994), 21–30.
-/

@[expose] public section

namespace Erdos81

open SimpleGraph

/-- Let $G$ be a chordal graph on $n$ vertices - that is, $G$ has no induced cycles of
length greater than $3$. Can the edges of $G$ be partitioned into $n^2/6+O(n)$ many cliques?

The answer is yes: in fact $\lfloor n(n+1)/6\rfloor$ cliques suffice for all sufficiently
large $n$ (see [erdosproblems.com/81](https://www.erdosproblems.com/81)). The corollary gives
the $n^2/6+Cn$ bound for every $n$, which is the statement below.

A Lean 4 formalisation is available at
[N0zoM1z0/erdos-81](https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/lean/Erdos81/MainTheorem.lean#L125),
conditional on Vizing's theorem, the Häggkvist–Janssen list-edge-colouring bound, and a
packing-transfer interface that includes LP attainment
(`erdos81_of_inputs` in
[ExternalInputs.lean](https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/lean/Erdos81/ExternalInputs.lean)).
-/
@[category research solved, question, AMS 5]
theorem erdos_81 :
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.IsChordal →
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧
        (P.card : ℝ) ≤ (n : ℝ) ^ 2 / 6 + C * n := by
  sorry

/-- Chen, Erdős, and Ordman [CEO94] have shown that any split graph can be partitioned
into $\frac{3}{16}n^2+O(n)$ many cliques. -/
@[category research solved, AMS 5]
theorem erdos_81.variants.split :
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.IsSplitGraph →
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧
        (P.card : ℝ) ≤ 3 * (n : ℝ) ^ 2 / 16 + C * n := by
  sorry

end Erdos81
