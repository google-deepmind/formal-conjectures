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
# Erdős Problem 716

*Reference:* [erdosproblems.com/716](https://www.erdosproblems.com/716)

Let $\mathcal{F}$ be the family of all 3-uniform hypergraphs on 6 vertices with 3 edges.
Is it true that $\mathrm{ex}_3(n, \mathcal{F}) = o(n^2)$? A conjecture of Brown, Erdős,
and Sós [BES73], answered affirmatively by Ruzsa and Szemerédi [RuSz78]. This is known as
the Ruzsa–Szemerédi problem.

See also Problem 1178 for the generalisation to $k$ vertices and $k-3$ edges, and
Problem 1157 for the completely general Brown–Erdős–Sós conjecture.

[BES73] Brown, W.G., Erdős, P., and Sós, V.T., *Some extremal problems on r-graphs*.
(1973), 53-63.

[RuSz78] Ruzsa, I.Z. and Szemerédi, E., *Triple systems with no six points carrying three
triangles*. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II
(1978), 939-945.
-/

namespace Erdos716

/-- A 3-uniform hypergraph on `Fin n`: a family of 3-element subsets. -/
structure Hypergraph3 (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- A 3-uniform hypergraph is $\mathcal{F}$-free (where $\mathcal{F}$ is the family of all
3-uniform hypergraphs on 6 vertices with 3 edges) if every 6-element subset of
vertices contains at most 2 edges. -/
def Hypergraph3.isFamilyFree {n : ℕ} (H : Hypergraph3 n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 6 →
    (H.edges.filter (· ⊆ S)).card ≤ 2

/-- **Erdős Problem 716** (Brown-Erdős-Sós conjecture [BES73], proved by Ruzsa-Szemerédi
[RuSz78]): $\mathrm{ex}_3(n, \mathcal{F}) = o(n^2)$, i.e., for any $\varepsilon > 0$,
every sufficiently large $\mathcal{F}$-free 3-uniform hypergraph on $n$ vertices has at most
$\varepsilon \cdot n^2$ edges. -/
@[category research solved, AMS 5]
theorem erdos_716 : answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : Hypergraph3 n, H.isFamilyFree →
    (H.edges.card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos716
