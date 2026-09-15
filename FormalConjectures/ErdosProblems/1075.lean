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
# Erdős Problem 1075

*References:*
- [erdosproblems.com/1075](https://www.erdosproblems.com/1075)
- [Er64f] Erdős, P., *On extremal problems of graphs and generalized graphs*.
  Israel J. Math. (1964), 183–190.
- [Gu26] Gu, Q., [Counterexamples to Erdős Problem 1075](https://github.com/FireflySentinel/erdos-1075/blob/1bdd7b6fb62b9d65f425a77cf6e804b7fadc7fc8/paper/PROOF.pdf) (2026).
-/

open Filter

namespace Erdos1075

/-- The density-increment assertion at uniformity $r$. Requiring arbitrarily large
prescribed lower bounds on the subgraph order expresses $m(n)\to\infty$.
The finite family $E$ represents a simple hypergraph on $\operatorname{Fin} n$. -/
def HasDensityIncrement (r : ℕ) : Prop :=
  ∃ c : ℝ, 1 / (r : ℝ) ^ r < c ∧ ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
    ∀ᶠ n : ℕ in atTop, ∀ E : Finset (Finset (Fin n)),
      (∀ e ∈ E, e.card = r) →
      (1 + ε) * ((n : ℝ) / (r : ℝ)) ^ r ≤ (E.card : ℝ) →
      ∃ S : Finset (Fin n), m ≤ S.card ∧
        c * (S.card : ℝ) ^ r ≤ ((E.filter (fun e => e ⊆ S)).card : ℝ)

/--
Let $r\geq 3$. There exists $c_r>r^{-r}$ such that, for any $\epsilon>0$, if $n$ is
sufficiently large, the following holds.

Any $r$-uniform hypergraph on $n$ vertices with at least $(1+\epsilon)(n/r)^r$ many
edges contains a subgraph on $m$ vertices with at least $c_rm^r$ edges, where
$m=m(n)\to \infty$ as $n\to \infty$.

Gu [Gu26] gives counterexamples for every $r\geq5$. The cases $r=3,4$ remain open.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/FireflySentinel/erdos-1075/blob/1bdd7b6fb62b9d65f425a77cf6e804b7fadc7fc8/checks/FormalConjecturesBridge.lean#L44"]
theorem erdos_1075 :
    ¬∀ r : ℕ, 3 ≤ r → HasDensityIncrement r := by
  sorry

/-- The density-increment assertion fails for every uniformity $r\geq5$ [Gu26]. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/FireflySentinel/erdos-1075/blob/1bdd7b6fb62b9d65f425a77cf6e804b7fadc7fc8/checks/FormalConjecturesBridge.lean#L28"]
theorem erdos_1075.variants.r_ge_five :
    ∀ r : ℕ, 5 ≤ r → ¬HasDensityIncrement r := by
  sorry

end Erdos1075
