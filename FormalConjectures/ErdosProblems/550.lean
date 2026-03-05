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
# Erdős Problem 550

*Reference:* [erdosproblems.com/550](https://www.erdosproblems.com/550)

Let $m_1 \le \cdots \le m_k$ and $n$ be sufficiently large. If $T$ is a tree on $n$ vertices
and $G$ is the complete multipartite graph with vertex class sizes $m_1, \ldots, m_k$, then
$$R(T, G) \le (\chi(G) - 1)(R(T, K_{m_1,m_2}) - 1) + m_1.$$

For a complete $k$-partite graph with $k \ge 2$ non-empty parts, $\chi(G) = k$, so the
bound becomes $(k - 1)(R(T, K_{m_1,m_2}) - 1) + m_1$.

Chvátal [Ch77] proved that $R(T, K_m) = (m - 1)(n - 1) + 1$.

[EFRS85] Erdős, P., Faudree, R., Rousseau, C., and Schelp, R.,
*Multipartite graph—sparse graph Ramsey numbers*, Combinatorica **5** (1985), 311–318.

[Ch77] Chvátal, V., *Tree-complete graph Ramsey numbers*,
J. Graph Theory **1** (1977), 93.
-/

open SimpleGraph

namespace Erdos550

/-- A graph $H$ contains a copy of graph $G$ (as a subgraph) if there is an injective
function from $V(G)$ to $V(H)$ that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The off-diagonal Ramsey number $R(G_1, G_2)$: the minimum $N$ such that every
graph $H$ on $N$ vertices contains a copy of $G_1$ or its complement contains a
copy of $G_2$. -/
noncomputable def offDiagRamseyNumber {V₁ V₂ : Type*}
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G₁ H ∨ ContainsSubgraphCopy G₂ Hᶜ}

/-- The complete multipartite graph with vertex class sizes given by `sizes`.
Vertices are pairs $(i, j)$ where $i$ indexes the part and $j$ is within the part.
Two vertices are adjacent iff they belong to different parts. -/
def completeMultipartiteGraph {k : ℕ} (sizes : Fin k → ℕ) :
    SimpleGraph (Σ i : Fin k, Fin (sizes i)) where
  Adj v w := v.1 ≠ w.1
  symm _ _ h := Ne.symm h
  loopless _ := fun h => h rfl

/-- Part sizes for the complete bipartite graph $K_{m_1,m_2}$. -/
def bipSizes (m₁ m₂ : ℕ) : Fin 2 → ℕ
  | ⟨0, _⟩ => m₁
  | ⟨_ + 1, _⟩ => m₂

/--
Erdős Problem 550 [EFRS85]:

Let $m_1 \le \cdots \le m_k$ and $n$ be sufficiently large. If $T$ is a tree on $n$ vertices and
$G$ is the complete multipartite graph with vertex class sizes $m_1, \ldots, m_k$, then
$$R(T, G) \le (\chi(G) - 1)(R(T, K_{m_1,m_2}) - 1) + m_1.$$

For a complete $k$-partite graph with non-empty parts, $\chi(G) = k$, so the bound
becomes $(k - 1) \cdot (R(T, K_{m_1,m_2}) - 1) + m_1$, where $K_{m_1,m_2}$ is the
complete bipartite graph with part sizes $m_1$ (= `sizes 0`) and $m_2$ (= `sizes 1`).
-/
@[category research open, AMS 5]
theorem erdos_550 (k : ℕ) (hk : k ≥ 2) (sizes : Fin k → ℕ)
    (hsizes_pos : ∀ i, 0 < sizes i)
    (hsizes_mono : Monotone sizes) :
    let m₁ := sizes ⟨0, by omega⟩
    let m₂ := sizes ⟨1, by omega⟩
    ∃ N₀ : ℕ, ∀ (n : ℕ), n ≥ N₀ →
    ∀ (T : SimpleGraph (Fin n)), T.IsTree →
      offDiagRamseyNumber T (completeMultipartiteGraph sizes) ≤
        (k - 1) * (offDiagRamseyNumber T
          (completeMultipartiteGraph (bipSizes m₁ m₂)) - 1) + m₁ := by
  sorry

end Erdos550
