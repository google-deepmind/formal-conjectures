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
# Erdős Problem 1036

*Reference:* [erdosproblems.com/1036](https://www.erdosproblems.com/1036)

A question of Erdős and Rényi. Proved by Shelah [Sh98].

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős is eighty,
Vol. 2 (Keszthely, 1993), p.346.

[Sh98] Shelah, S., _Erdős and Rényi conjecture_. J. Combin. Theory Ser. A 82 (1998), no. 2,
179–185.
-/

open SimpleGraph Finset

namespace Erdos1036

/--
**Erdős Problem 1036** (Proved by Shelah [Sh98]) [Er93, p.346]:

For every $c > 0$, there exist $\delta > 0$ and $N_0$ such that for all $n \geq N_0$, if $G$ is a
graph on $n$ vertices with no clique and no independent set of size greater than
$c \cdot \log n$, then $G$ has at least $2^{\delta n}$ pairwise non-isomorphic induced subgraphs.

Here "trivial graph" means empty (independent set) or complete (clique), and
$\log$ denotes the natural logarithm.
-/
@[category research solved, AMS 5]
theorem erdos_1036 :
    answer(True) ↔
    ∀ c : ℝ, c > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      ∃ F : Finset (Finset (Fin n)),
        (F.card : ℝ) ≥ (2 : ℝ) ^ (δ * (n : ℝ)) ∧
        ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
          ¬Nonempty (G.induce (↑S : Set (Fin n)) ≃g G.induce (↑T : Set (Fin n))) := by
  sorry

end Erdos1036
