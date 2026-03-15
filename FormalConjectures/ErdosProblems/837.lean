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
# Erdős Problem 837

*Reference:* [erdosproblems.com/837](https://www.erdosproblems.com/837)

Let $k \geq 2$ and $A_k \subseteq [0,1]$ be the set of $\alpha$ such that there exists some
$\beta(\alpha) > \alpha$ with the property that, if $G_1, G_2, \ldots$ is a sequence of $k$-uniform
hypergraphs with
$$\liminf \frac{e(G_n)}{\binom{|G_n|}{k}} > \alpha$$
then there exist subgraphs $H_n \subseteq G_n$ such that $|H_n| \to \infty$ and
$$\liminf \frac{e(H_n)}{\binom{|H_n|}{k}} > \beta,$$
and further that this property does not necessarily hold if $> \alpha$ is
replaced by $\geq \alpha$.

It is known that $A_2 = \{1 - 1/m : m \geq 1\}$ (Erdős-Stone-Simonovits).

What is $A_3$?

[Er74d] Erdős, P. and Simonovits, M., problem on hypergraph density jumps.
-/

open Finset

namespace Erdos837

/-- A $k$-uniform hypergraph on $n$ vertices: a collection of $k$-element subsets
    of $\operatorname{Fin}(n)$. -/
structure UniformHypergraph (n k : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = k

/-- The edge density of a $k$-uniform hypergraph: $|E| / \binom{n}{k}$. -/
noncomputable def UniformHypergraph.density {n k : ℕ}
    (G : UniformHypergraph n k) : ℝ :=
  if Nat.choose n k = 0 then 0
  else (G.edges.card : ℝ) / (Nat.choose n k : ℝ)

/-- $H$ is a sub-hypergraph of $G$ via an injective vertex map $f$,
    meaning every edge of $H$ maps to an edge of $G$ under $f$. -/
def UniformHypergraph.IsSubgraphVia {m n k : ℕ} (H : UniformHypergraph m k)
    (G : UniformHypergraph n k) (f : Fin m ↪ Fin n) : Prop :=
  ∀ e ∈ H.edges, e.map f ∈ G.edges

/-- The density jump set $A_k$ for $k$-uniform hypergraphs.
    $\alpha \in A_k$ iff there exists $\beta > \alpha$ such that:
    (a) any sequence of $k$-uniform hypergraphs with $\liminf$ density $> \alpha$
        contains growing subgraphs with $\liminf$ density $> \beta$;
    (b) this does NOT hold when the hypothesis is weakened to $\liminf$ density $\geq \alpha$. -/
def densityJumpSet (k : ℕ) : Set ℝ :=
  {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧
    ∃ β : ℝ, β > α ∧
      -- (a) Density jump: liminf density > α implies dense growing subgraphs
      (∀ (sizes : ℕ → ℕ) (G : ∀ i, UniformHypergraph (sizes i) k),
        -- Hypothesis: |Gᵢ| → ∞
        (∀ M : ℕ, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → sizes i ≥ M) →
        -- Hypothesis: liminf density(Gᵢ) > α
        (∃ δ : ℝ, δ > 0 ∧ ∃ N₀ : ℕ, ∀ i : ℕ, i ≥ N₀ →
          (G i).density ≥ α + δ) →
        -- Conclusion: ∃ subgraphs Hᵢ with |Hᵢ| → ∞ and liminf density > β
        ∃ (subSizes : ℕ → ℕ) (H : ∀ i, UniformHypergraph (subSizes i) k),
          (∀ M : ℕ, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → subSizes i ≥ M) ∧
          (∀ i, ∃ f : Fin (subSizes i) ↪ Fin (sizes i),
            (H i).IsSubgraphVia (G i) f) ∧
          (∃ δ' : ℝ, δ' > 0 ∧ ∃ N₁ : ℕ, ∀ i : ℕ, i ≥ N₁ →
            (H i).density ≥ β + δ')) ∧
      -- (b) Fails with ≥ α
      ¬(∀ (sizes : ℕ → ℕ) (G : ∀ i, UniformHypergraph (sizes i) k),
        -- Hypothesis: |Gᵢ| → ∞
        (∀ M : ℕ, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → sizes i ≥ M) →
        (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ i : ℕ, i ≥ N₀ →
          (G i).density ≥ α - ε) →
        ∃ (subSizes : ℕ → ℕ) (H : ∀ i, UniformHypergraph (subSizes i) k),
          (∀ M : ℕ, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → subSizes i ≥ M) ∧
          (∀ i, ∃ f : Fin (subSizes i) ↪ Fin (sizes i),
            (H i).IsSubgraphVia (G i) f) ∧
          (∃ δ' : ℝ, δ' > 0 ∧ ∃ N₁ : ℕ, ∀ i : ℕ, i ≥ N₁ →
            (H i).density ≥ β + δ'))}

/-- Known: $A_2 = \{1 - 1/m : m \geq 1\}$ (Erdős-Stone-Simonovits density jump). -/
@[category research solved, AMS 5]
theorem erdos_837.variants.graphs :
    densityJumpSet 2 = {α : ℝ | ∃ m : ℕ, m ≥ 1 ∧ α = 1 - 1 / (m : ℝ)} := by
  sorry

/--
Erdős Problem 837 [Er74d]:
Determine the density jump set $A_3$ for $3$-uniform hypergraphs.

It is known that $A_2 = \{1 - 1/m : m \geq 1\}$ by the Erdős-Stone-Simonovits theorem.
The analogous characterization of $A_3$ is open.
-/
@[category research open, AMS 5]
theorem erdos_837 :
    densityJumpSet 3 = answer(sorry) := by
  sorry

end Erdos837
