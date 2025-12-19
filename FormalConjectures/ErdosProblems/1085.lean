/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1085

Let f_d(n) be minimal such that, in any set of n points in ℝ^d, there exist at most f_d(n) pairs
of points which are distance 1 apart. Estimate f_d(n).

*Reference:* [erdosproblems.com/1085](https://www.erdosproblems.com/1085)
-/

namespace Erdos1085

open EuclideanSpace Finset

variable {d : ℕ}

/--
The number of pairs of points in a finite set `S` of points in `ℝ^d` that are distance 1 apart.
-/
noncomputable def countUnitDistancePairs (d : ℕ) (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  #(S.sym2.filter fun s => dist s.out.1 s.out.2 = 1)

/--
The minimal value f_d(n) such that for any set of n points in ℝ^d, there exist at most f_d(n)
pairs of points which are distance 1 apart.
-/
noncomputable def f_d (d n : ℕ) : ℕ :=
  ⨆ (S : Finset (EuclideanSpace ℝ (Fin d))) (_ : S.card = n), countUnitDistancePairs d S

/--
Estimate f_d(n). Find the best possible constants c₁, c₂, α, β such that
c₁ * n^α ≤ f_d(n) ≤ c₂ * n^β for all sufficiently large n.

Known results:
- For d=2: f_2(n) = O(n^(4/3)) and f_2(n) = Ω(n^(1+c/log log n)) for some c > 0
- For d≥3: f_d(n) = Θ(n^(2-2/d)) (Spencer-Szemerédi-Trotter)
-/
@[category research open, AMS 52]
theorem erdos_1085 :
    (∀ d n : ℕ, n > 0 → f_d d n ≤ answer(sorry) * n ^ answer(sorry)) ∧
    (∀ d n : ℕ, n > answer(sorry) → f_d d n ≥ answer(sorry) * n ^ answer(sorry)) := by
  sorry

end Erdos1085
