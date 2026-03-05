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
# Erdős Problem 934

*Reference:* [erdosproblems.com/934](https://www.erdosproblems.com/934)

Let $h_t(d)$ be minimal such that every graph $G$ with $h_t(d)$ edges and
maximal degree $\leq d$ contains two edges whose shortest path between them
has length $\geq t$.

Estimate $h_t(d)$.

A problem of Erdős and Nešetřil [Er88]. Known:
- $h_t(d) \leq 2d^t$ always and $h_1(d) = d + 1$
- $h_2(d) \leq \frac{5}{4}d^2 + 1$ (Chung–Gyárfás–Tuza–Trotter [CGTT90])
- $h_t(d) \leq \frac{3}{2}d^t + 1$ for all $t \geq 1$ [CCJK22]

Cambie–Cames van Batenburg–de Joannis de Verclos–Kang [CCJK22] conjecture
that, for all $t \geq 3$, $h_t(d) \sim d^t$ as $d \to \infty$:
$h_t(d) \leq (1 + o(1))d^t$ for all $d$ and
$h_t(d) \geq (1 - o(1))d^t$ for infinitely many $d$.

[Er88] Erdős, P. and Nešetřil, J., _Irregularities of partitions_ (1989).

[CGTT90] Chung, F.R.K., Gyárfás, A., Tuza, Z., and Trotter, W.T., _The maximum number of edges
in $2K_2$-free graphs of bounded degree_. Discrete Mathematics (1990).

[CCJK22] Cambie, S., Cames van Batenburg, W., de Joannis de Verclos, R., and Kang, R.J.,
_Packing graphs of bounded codegree_ (2022).
-/

open SimpleGraph Classical

namespace Erdos934

/-- Two edges $e_1$, $e_2$ in a simple graph $G$ are at distance at least $t$:
for every endpoint $u$ of $e_1$ and $v$ of $e_2$ that lie in the same connected
component, $t \leq \operatorname{dist}_G(u, v)$. (Endpoints in different components are
considered infinitely far apart and satisfy any finite distance bound.) -/
def EdgesAtDist {V : Type*} (G : SimpleGraph V) (e₁ e₂ : Sym2 V) (t : ℕ) : Prop :=
  ∀ u, u ∈ e₁ → ∀ v, v ∈ e₂ → G.Reachable u v → t ≤ G.dist u v

/-- Erdős Problem 934, upper bound direction of the asymptotic conjecture [CCJK22]:
For all $t \geq 3$ and $\varepsilon > 0$, for all sufficiently large $d$, every finite graph
with maximum degree $\leq d$ and more than $(1 + \varepsilon) \cdot d^t$ edges contains two
distinct edges at distance $\geq t$. -/
@[category research open, AMS 5]
theorem erdos_934 :
    ∀ t : ℕ, 3 ≤ t →
    ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d →
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.maxDegree ≤ d →
      (G.edgeFinset.card : ℝ) > (1 + ε) * (d : ℝ) ^ t →
      ∃ e₁ ∈ G.edgeSet, ∃ e₂ ∈ G.edgeSet,
        e₁ ≠ e₂ ∧ EdgesAtDist G e₁ e₂ t := by
  sorry

/-- Erdős Problem 934, lower bound direction of the asymptotic conjecture [CCJK22]:
For all $t \geq 3$ and $\varepsilon > 0$, there are infinitely many $d$ for which some graph
with maximum degree $\leq d$ and at least $(1 - \varepsilon) \cdot d^t$ edges has no pair of
distinct edges at distance $\geq t$. -/
@[category research open, AMS 5]
theorem erdos_934.variants.lower_bound :
    ∀ t : ℕ, 3 ≤ t →
    ∀ ε : ℝ, 0 < ε →
    ∀ D₀ : ℕ, ∃ d : ℕ, D₀ ≤ d ∧
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ d ∧
      (G.edgeFinset.card : ℝ) ≥ (1 - ε) * (d : ℝ) ^ t ∧
      ¬∃ e₁ ∈ G.edgeSet, ∃ e₂ ∈ G.edgeSet,
        e₁ ≠ e₂ ∧ EdgesAtDist G e₁ e₂ t := by
  sorry

end Erdos934
