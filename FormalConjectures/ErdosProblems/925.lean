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
# Erdős Problem 925

*Reference:* [erdosproblems.com/925](https://www.erdosproblems.com/925)

Is there a constant $\delta > 0$ such that, for all large $n$, if $G$ is a graph on $n$
vertices which is not Ramsey for $K_3$ (i.e. there exists a 2-colouring of the
edges of $G$ with no monochromatic triangle) then $G$ contains an independent set
of size $\gg n^{1/3+\delta}$?

It is easy to show that there exists an independent set of size $\gg n^{1/3}$.

Equivalently, this asks whether $R(3,3,m) \ll m^{3-c}$ for some $c > 0$.

DISPROVED by Alon and Rödl [AlRo05], who proved that
$$m^3 / (\log m)^{4+o(1)} \ll R(3,3,m) \ll m^3 / (\log m)^2.$$
Sudakov observed that the $\log \log m$ in the upper bound can be removed.

[Er69b] Erdős, P.

[AlRo05] Alon, N. and Rödl, V., _Sharp bounds for some multicolor Ramsey numbers_,
Combinatorica 25 (2005), 125-141.
-/

open SimpleGraph

namespace Erdos925

/-- A graph $G$ on $n$ vertices is "not Ramsey for $K_3$" if there exists a
2-colouring of its edges with no monochromatic triangle. Equivalently,
there is a subgraph $H \leq G$ such that both $H$ and $G \setminus H$ are triangle-free. -/
def IsNotRamseyForTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.CliqueFree 3 ∧ (G \ H).CliqueFree 3

/--
Erdős Problem 925 [Er69b] (DISPROVED by Alon-Rödl [AlRo05]):

There exists $\delta > 0$ and $C > 0$ such that for all sufficiently large $n$, every
graph $G$ on $n$ vertices which is not Ramsey for $K_3$ contains an independent set
of size at least $C \cdot n^{1/3 + \delta}$.
-/
@[category research solved, AMS 5]
theorem erdos_925 : answer(False) ↔
    ∃ δ : ℝ, δ > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ G : SimpleGraph (Fin n), IsNotRamseyForTriangle G →
        ∃ S : Finset (Fin n),
          (S.card : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v := by
  sorry

end Erdos925
