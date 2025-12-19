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
  #(S.offDiag.filter fun (p, q) => dist p q = 1)

/--
The minimal value f_d(n) such that for any set of n points in ℝ^d, there exist at most f_d(n)
pairs of points which are distance 1 apart.
-/
noncomputable def f_d (d n : ℕ) : ℕ :=
  ⨆ (S : Finset (EuclideanSpace ℝ (Fin d))) (_ : S.card = n), countUnitDistancePairs d S

/--
Estimate f_d(n). This asks for good upper and lower bounds on f_d(n) as a function of n and d.
-/
@[category research open, AMS 52]
theorem erdos_1085 :
    (∃ bounds : ℕ → ℕ → ℕ, ∀ d n : ℕ, f_d d n ≤ bounds d n) ↔ answer(sorry) := by
  sorry

end Erdos1085
