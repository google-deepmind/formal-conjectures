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
# Erdős Problem 1083

*Reference:* [erdosproblems.com/1083](https://www.erdosproblems.com/1083)

Let $d \geq 3$, and let $f_d(n)$ be the minimal $m$ such that every set of $n$ points
in $\mathbb{R}^d$ determines at least $m$ distinct distances. Is it true that
$f_d(n) = n^{2/d - o(1)}$?

Erdős [Er46b] proved $n^{1/d} \ll_d f_d(n) \ll_d n^{2/d}$, the upper bound
construction being given by a set of lattice points.

[Er46b] Erdős, P., _On sets of distances of n points_, 1946.

[Er75f] Erdős, P., _Problems and results in combinatorial geometry_, 1975.
-/

namespace Erdos1083

/-- The number of distinct pairwise distances determined by a finite point set
in $\mathbb{R}^d$. -/
noncomputable def distinctDistanceCountInDim (d : ℕ) (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  Set.ncard {r : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ r = dist p q}

/-- $f_d(n)$: the minimal number of distinct distances determined by any set of
$n$ points in $\mathbb{R}^d$. -/
noncomputable def minDistinctDistances (d : ℕ) (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (P : Finset (EuclideanSpace ℝ (Fin d))),
    P.card = n ∧ distinctDistanceCountInDim d P = m}

/--
**Erdős Problem 1083** [Er46b][Er75f, p.101]:

For all $d \geq 3$ and $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$,
$f_d(n) \geq n^{2/d - \varepsilon}$.

This is the conjectured lower bound part of $f_d(n) = n^{2/d - o(1)}$.
The matching upper bound $f_d(n) \ll_d n^{2/d}$ was proved by Erdős via
lattice points.
-/
@[category research open, AMS 52]
theorem erdos_1083 (d : ℕ) (hd : d ≥ 3) (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (minDistinctDistances d n : ℝ) ≥ (n : ℝ) ^ ((2 : ℝ) / d - ε) := by
  sorry

end Erdos1083
