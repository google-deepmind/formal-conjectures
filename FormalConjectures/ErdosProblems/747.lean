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
# Erdős Problem 747

*Reference:* [erdosproblems.com/747](https://www.erdosproblems.com/747)

Shamir's problem (1979): How large should $\ell(n)$ be such that, almost surely, a random
$3$-uniform hypergraph on $3n$ vertices with $\ell(n)$ edges must contain $n$ vertex-disjoint
edges?

[JKV08] Johansson, A., Kahn, J., and Vu, V., _Factors in random graphs_, Random Structures
& Algorithms 33 (2008), 1-28.

[Ka23] Kahn, J., _Asymptotics for Shamir's problem_, Annals of Mathematics 198 (2023), 1-69.
-/

open scoped Classical
open Finset

namespace Erdos747

/-- The set of all $3$-element subsets of $\operatorname{Fin} N$ (potential hyperedges). -/
def threeEdges (N : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.powerset.filter (fun s => s.card = 3)

/-- The set of all $3$-uniform hypergraphs on $\operatorname{Fin} N$ with exactly $m$ edges. -/
def hypergraphsWithEdges (N m : ℕ) : Finset (Finset (Finset (Fin N))) :=
  (threeEdges N).powerset.filter (fun H => H.card = m)

/-- A $3$-uniform hypergraph $H$ contains a matching of size $k$: there exist
    $k$ pairwise vertex-disjoint edges in $H$. -/
def HasMatching {N : ℕ} (H : Finset (Finset (Fin N))) (k : ℕ) : Prop :=
  ∃ M : Finset (Finset (Fin N)), M ⊆ H ∧ M.card = k ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- The fraction of $3$-uniform hypergraphs on $\operatorname{Fin} N$ with $m$ edges that
    contain a matching of size $k$. Returns $0$ if no such hypergraphs exist. -/
noncomputable def hypergraphMatchingFraction (N m k : ℕ) : ℝ :=
  ((hypergraphsWithEdges N m).filter (fun H => HasMatching H k)).card /
  ((hypergraphsWithEdges N m).card : ℝ)

/--
Erdős Problem 747 (Shamir's problem):

For every $\varepsilon > 0$, almost surely a random $3$-uniform hypergraph on $3n$ vertices
with at least $(1 + \varepsilon) \cdot n \cdot \log n$ edges contains $n$ vertex-disjoint edges.

Formally: for every $\varepsilon > 0$ and $\delta > 0$, there exists $n_0$ such that for all
$n \geq n_0$ and all $m$ with $(1 + \varepsilon) \cdot n \cdot \log n \leq m \leq \binom{3n}{3}$,
the fraction of $3$-uniform hypergraphs on $3n$ vertices with $m$ edges containing a perfect
matching is at least $1 - \delta$.

Proved by Johansson, Kahn, and Vu [JKV08]; sharp threshold by Kahn [Ka23].
-/
@[category research solved, AMS 5]
theorem erdos_747 :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ m : ℕ, (m : ℝ) ≥ (1 + ε) * (n : ℝ) * Real.log (n : ℝ) →
        m ≤ (3 * n).choose 3 →
        hypergraphMatchingFraction (3 * n) m n ≥ 1 - δ := by
  sorry

end Erdos747
