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
# Erdős Problem 812

*Reference:* [erdosproblems.com/812](https://www.erdosproblems.com/812)

Is it true that $R(n+1)/R(n) \geq 1 + c$ for some constant $c > 0$, for all large $n$?
Is it true that $R(n+1) - R(n) \gg n^2$?

Here $R(n)$ denotes the diagonal Ramsey number $R(n,n)$: the minimum $N$ such that
every simple graph on $N$ vertices contains either a clique of size $n$ or an
independent set of size $n$.

[BEFS89] Burr, S.A., Erdős, P., Faudree, R.J., and Schelp, R.H., proved that
$R(n+1) - R(n) \geq 4n - 8$ for all $n \geq 2$.

[Er91] Erdős, P., _Problems and results on graphs and hypergraphs_, 1991.
-/

open SimpleGraph

namespace Erdos812

/-- The diagonal Ramsey number $R(n) = R(n,n)$: the minimum $N$ such that every
simple graph on $N$ vertices contains either an $n$-clique or an independent
set of size $n$ (an $n$-clique in the complement). -/
noncomputable def diagonalRamsey (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree n ∨ ¬Gᶜ.CliqueFree n}

/--
**Erdős Problem 812, Part 1** [Er91]:

Is it true that there exists a constant $c > 0$ such that $R(n+1)/R(n) \geq 1 + c$ for all
sufficiently large $n$? That is, do the diagonal Ramsey numbers grow at least
geometrically?
-/
@[category research open, AMS 5]
theorem erdos_812 : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (diagonalRamsey (n + 1) : ℝ) / (diagonalRamsey n : ℝ) ≥ 1 + c := by
  sorry

/--
**Erdős Problem 812, Part 2** [Er91]:

Is it true that $R(n+1) - R(n) \gg n^2$, i.e., there exists a constant $c > 0$ such that
$R(n+1) - R(n) \geq c \cdot n^2$ for all sufficiently large $n$?
-/
@[category research open, AMS 5]
theorem erdos_812.variants.quadratic_gap : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (diagonalRamsey (n + 1) : ℝ) - (diagonalRamsey n : ℝ) ≥ c * (n : ℝ) ^ 2 := by
  sorry

end Erdos812
