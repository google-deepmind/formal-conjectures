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
import FormalConjecturesForMathlib.Combinatorics.Basic

/-!
# Ben Green's Open Problem 6

*Reference:* [Ben Green's Open Problem 6](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.6)

Fix an integer d. What is the largest sum-free subset of [N]^d?
-/

open Set Fintype

namespace Green6

/-- The grid [N]^d, represented as vectors in ℕ^d with components in [1, N]. -/
def Grid (N d : ℕ) : Set (Fin d → ℕ) :=
  {v | ∀ i, v i ∈ Icc 1 N}

/-- The size of the largest sum-free subset of [N]^d. -/
noncomputable def MaxSumFreeSubsetSize (N d : ℕ) : ℕ :=
  sSup {n | ∃ (A : Finset (Fin d → ℕ)), (A : Set (Fin d → ℕ)) ⊆ Grid N d ∧ IsSumFree (A : Set (Fin d → ℕ)) ∧ A.card = n}

/--
Fix an integer $d$. What is the largest sum-free subset of $[N]^d$?
We interpret this as asking for the asymptotic density of the largest sum-free subset.
-/
@[category research open, AMS 11]
theorem green_6 (d : ℕ) : answer(sorry) ↔
    ∃ (c : ℝ), Filter.Tendsto (fun N ↦ (MaxSumFreeSubsetSize N d : ℝ) / N^d) Filter.atTop (nhds c) := by
  sorry

end Green6
