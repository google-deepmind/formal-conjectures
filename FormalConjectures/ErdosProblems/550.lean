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
# Erdős Problem 550

*References:*
- [erdosproblems.com/550](https://www.erdosproblems.com/550)
- [Ch77] Chvátal, V., Tree-complete graph Ramsey numbers. J. Graph Theory (1977), 93.
- [Li26] Li, E., *A Resolution of Erdős Problem 550 on Tree versus Complete Multipartite Ramsey
  Numbers*, [arXiv:2606.23659](https://arxiv.org/abs/2606.23659) (2026).
-/

open Filter

namespace Erdos550

/--
Let $m_1\leq\cdots\leq m_k$ and $n$ be sufficiently large. If $T$ is a tree on $n$ vertices
and $G$ is the complete multipartite graph with vertex class sizes $m_1,\ldots,m_k$ then prove that
$$R(T,G)\leq (\chi(G)-1)(R(T,K_{m_1,m_2})-1)+m_1.$$

This problem is #16 in Ramsey Theory in the graphs problem collection.

Li [Li26] proved this, combining an off-Turán tree-embedding theorem with a compactness theorem
for bounded-rank hypergraph obstructions. The linked formal proof states the bound for trees on an
arbitrary finite vertex type and with `K_{m_1,m_2}` written as a complete multipartite graph with
two parts; the statement below is the special case `V = Fin n`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos550/Main.lean#L80"]
theorem erdos_550 :
    ∀ (k : ℕ) (hk : 2 ≤ k) (m : Fin k → ℕ) (hm : Monotone m)
      (hm_pos : ∀ i, 0 < m i),
      ∀ᶠ n : ℕ in atTop,
        ∀ (T : SimpleGraph (Fin n)), T.IsTree →
          SimpleGraph.graphRamsey T
            (SimpleGraph.completeMultipartiteGraph (fun i ↦ Fin (m i))) ≤
            (k - 1) * (SimpleGraph.graphRamsey T
              (completeBipartiteGraph (Fin (m ⟨0, by omega⟩)) (Fin (m ⟨1, by omega⟩))) - 1) +
                m ⟨0, by omega⟩ := by
  sorry

-- TODO: Add variants of the problem.

end Erdos550
