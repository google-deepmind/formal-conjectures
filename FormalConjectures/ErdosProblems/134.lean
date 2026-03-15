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
# Erdős Problem 134

*Reference:* [erdosproblems.com/134](https://www.erdosproblems.com/134)

Let $\varepsilon, \delta > 0$ and $n$ be sufficiently large in terms of $\varepsilon$ and $\delta$.
Let $G$ be a triangle-free graph on $n$ vertices with maximum degree $< n^{1/2 - \varepsilon}$.

Can $G$ be made into a triangle-free graph with diameter $2$ by adding at most $\delta n^2$ edges?

Asked by Erdős and Gyárfás, who proved this is the case when $G$ has maximum degree
$\ll \log n / \log \log n$. A construction of Simonovits shows the conjecture fails if the
maximum degree bound is relaxed to $\leq Cn^{1/2}$ for a large enough constant $C$.

Proved in the affirmative by Alon [Al94]: a triangle-free graph on $n$ vertices with
maximum degree $< n^{1/2 - \varepsilon}$ can be made into a triangle-free graph with diameter $2$
by adding at most $O(n^{2 - \varepsilon})$ edges.

[Al94] Alon, N., _Explicit Ramsey graphs and orthonormal labelings_ (1994).

[Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_ (1997).

See also Problem 618.
-/

open Filter

namespace Erdos134

/-- A graph has diameter at most $2$ if every pair of distinct vertices is
either adjacent or shares a common neighbor. -/
def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v ∨ ∃ w : V, G.Adj u w ∧ G.Adj w v

/--
Erdős Problem 134 [Er97b] (proved by Alon [Al94]):

For every $\varepsilon, \delta > 0$ and all sufficiently large $n$, every triangle-free graph on
$n$ vertices with maximum degree $< n^{1/2 - \varepsilon}$ can be extended to a triangle-free
graph with diameter $\leq 2$ by adding at most $\delta n^2$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_134 :
    answer(True) ↔
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  sorry

/--
Erdős Problem 134 (Alon's strong form [Al94]):

For every $\varepsilon > 0$ there exists $C > 0$ such that for all sufficiently large $n$,
every triangle-free graph on $n$ vertices with maximum degree $< n^{1/2 - \varepsilon}$
can be extended to a triangle-free graph with diameter $\leq 2$ by adding at
most $C \cdot n^{2 - \varepsilon}$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_134.variants.alon_strong_form :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ (2 - ε) := by
  sorry

end Erdos134
