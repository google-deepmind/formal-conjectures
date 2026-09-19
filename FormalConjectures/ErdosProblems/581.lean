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
# Erdős Problem 581

*References:*
- [erdosproblems.com/581](https://www.erdosproblems.com/581)
- [CEG79] Chung, F. R. K. and Erdős, P. and Graham, R. L., _On the product of the point and line
  covering numbers of a graph_. Second International Conference on Combinatorial Mathematics
  (New York, 1978) (1979), 597-602.
- [Al96] Alon, Noga, _Bipartite subgraphs_. Combinatorica (1996), 301-311.
-/

@[expose] public section

open SimpleGraph

namespace Erdos581

/-- `f m` is the maximal `k` such that every triangle-free graph on `m` edges contains a
bipartite subgraph with `k` edges. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {k | ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    G.edgeSet.ncard = m → ∃ H ≤ G, H.IsBipartite ∧ k ≤ H.edgeSet.ncard}

/--
Let $f(m)$ be the maximal $k$ such that a triangle-free graph on $m$ edges must contain a
bipartite graph with $k$ edges. Determine $f(m)$.

Resolved by Alon [Al96], who showed that there exist constants $c_1,c_2>0$ such that
$$\frac{m}{2}+c_1m^{4/5}\leq f(m)\leq \frac{m}{2}+c_2m^{4/5}.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos581.lean#L31"]
theorem erdos_581 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ m : ℕ,
    (m : ℝ) / 2 + c₁ * (m : ℝ) ^ (4 / 5 : ℝ) ≤ f m ∧
      (f m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ (4 / 5 : ℝ) := by
  sorry

end Erdos581
