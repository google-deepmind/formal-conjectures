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
# Erdős Problem 571

Is it true that for every rational α ∈ [1, 2), there exists a bipartite graph G such that
the Turán extremal number satisfies ex(n; G) ≍ n^α?

*Reference:* [erdosproblems.com/571](https://www.erdosproblems.com/571)

[Er78] Erdős, P., _Problems and results in combinatorial analysis and combinatorial
  number theory_, Proceedings of the Ninth Southeastern Conference on Combinatorics,
  Graph Theory, and Computing (1978), 29–40.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
  Combinatorica **1** (1981), 25–42.

[ErSi84] Erdős, P. and Simonovits, M., _Cube-supersaturated graphs and related problems_,
  Progress in graph theory (Waterloo, Ont., 1982), Academic Press, Toronto, ON, 1984, 203–218.

[BuCo18] Bukh, B. and Conlon, D., _Rational exponents in extremal graph theory_,
  Journal of the European Mathematical Society (JEMS) (2018), 1747–1757.
-/

open SimpleGraph

namespace Erdos571

/-- A graph $G$ contains $H$ as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number $\mathrm{ex}(n; H)$: the maximum number of edges in a
simple graph on $n$ vertices that does not contain $H$ as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem 571 (Erdős–Simonovits):

For every rational $\alpha \in [1, 2)$, there exists a finite bipartite graph $G$ such that
the Turán extremal number satisfies $\mathrm{ex}(n; G) \asymp n^\alpha$, meaning there exist positive
constants $c_1, c_2 > 0$ and a threshold $N_0$ such that for all $n \geq N_0$,
$$c_1 \cdot n^\alpha \leq \mathrm{ex}(n; G) \leq c_2 \cdot n^\alpha.$$
-/
@[category research open, AMS 5]
theorem erdos_571 :
    ∀ α : ℚ, 1 ≤ α → α < 2 →
    ∃ (U : Type) (_ : Fintype U) (G : SimpleGraph U),
      G.Colorable 2 ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        c₁ * (n : ℝ) ^ (α : ℝ) ≤ (extremalNumber G n : ℝ) ∧
        (extremalNumber G n : ℝ) ≤ c₂ * (n : ℝ) ^ (α : ℝ) := by
  sorry

end Erdos571
