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
# Erdős Problem 546

*Reference:* [erdosproblems.com/546](https://www.erdosproblems.com/546)

Let $G$ be a graph with no isolated vertices and $m$ edges. Is it true that
$R(G) \leq 2^{O(m^{1/2})}$?

This is true, and was proved by Sudakov [Su11]. The analogous question for
$\geq 3$ colours is still open. A more precise question is Problem 545.

[Er84b] Erdős, P., _On some problems in graph theory, combinatorial analysis and
combinatorial number theory_. Graph theory and combinatorics (Cambridge, 1983),
Academic Press, London (1984), 1-17.

[Su11] Sudakov, B., _A conjecture of Erdős on graph Ramsey numbers_. Advances in
Mathematics 227 (2011), 601-609.
-/

open SimpleGraph

namespace Erdos546

/-- A graph $H$ contains a copy of graph $G$ (as a subgraph) if there is an injective
function from $V(G)$ to $V(H)$ that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The diagonal Ramsey number $R(G)$ for a graph $G$ on $\operatorname{Fin} k$: the minimum
$N$ such that every graph $H$ on $N$ vertices contains a copy of $G$ or its complement
contains a copy of $G$. -/
noncomputable def ramseyNumber {k : ℕ} (G : SimpleGraph (Fin k)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G H ∨ ContainsSubgraphCopy G Hᶜ}

/--
Erdős Problem 546 [Er84b, p.10]:

Let $G$ be a graph with no isolated vertices and $m$ edges. Is it true that
$R(G) \leq 2^{O(m^{1/2})}$?

Formally: there exists a constant $C > 0$ such that for every graph $G$ on $k$
vertices with no isolated vertices, $R(G) \leq 2^{C \cdot \sqrt{m}}$ where $m$ is the
number of edges.

This was proved by Sudakov [Su11].
-/
@[category research solved, AMS 5]
theorem erdos_546 : answer(True) ↔
    ∃ C : ℝ, C > 0 ∧
    ∀ (k : ℕ) (G : SimpleGraph (Fin k)),
      (∀ v : Fin k, ∃ w : Fin k, G.Adj v w) →
      (ramseyNumber G : ℝ) ≤ (2 : ℝ) ^ (C * Real.sqrt (G.edgeSet.ncard : ℝ)) := by
  sorry

end Erdos546
