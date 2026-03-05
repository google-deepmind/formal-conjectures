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
# Erdős Problem 751

*Reference:* [erdosproblems.com/751](https://www.erdosproblems.com/751)

Let $G$ be a graph with chromatic number $\chi(G) = 4$. If $m_1 < m_2 < \cdots$ are the
lengths of the cycles in $G$, can $\min(m_{i+1} - m_i)$ be arbitrarily large?

The answer is no: Bondy and Vince [BoVi98] proved that every graph with minimum degree
at least $3$ has two cycles whose lengths differ by at most $2$, and hence the same is
true for every graph with chromatic number $4$.

[BoVi98] Bondy, J. A. and Vince, A., _Cycles in a graph whose lengths differ by one or
two_. Journal of Graph Theory (1998), 11-15.
-/

open SimpleGraph

namespace Erdos751

/-- The set of cycle lengths occurring in a simple graph. -/
def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/-- **Erdős Problem 751**: If $G$ is a graph with $\chi(G) = 4$ and $m_1 < m_2 < \cdots$
are the cycle lengths of $G$, the minimum gap $\min(m_{i+1} - m_i)$ cannot be made
arbitrarily large. Bondy and Vince [BoVi98] proved that every graph with minimum degree
at least $3$ has two cycles whose lengths differ by at most $2$, which implies the
negative answer since $\chi(G) = 4$ forces a subgraph with minimum degree $\geq 3$.

[BoVi98] -/
@[category research solved, AMS 5]
theorem erdos_751 : answer(False) ↔
    (∀ C : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.chromaticNumber = 4 ∧
        ∀ m₁ ∈ cycleLengths G, ∀ m₂ ∈ cycleLengths G,
          m₁ < m₂ → C ≤ m₂ - m₁) := by
  sorry

/-- **Bondy–Vince Theorem**: Every graph with minimum degree at least $3$ contains two
cycles whose lengths differ by at most $2$. This is the stronger result that resolves
Erdős Problem 751.

[BoVi98] -/
@[category research solved, AMS 5]
theorem erdos_751.variants.bondy_vince {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    ∃ m₁ ∈ cycleLengths G, ∃ m₂ ∈ cycleLengths G,
      m₁ < m₂ ∧ m₂ - m₁ ≤ 2 := by
  sorry

end Erdos751
