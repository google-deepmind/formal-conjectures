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
# Erdős Problem 838

*Reference:* [erdosproblems.com/838](https://www.erdosproblems.com/838)
-/

namespace Erdos838

open scoped EuclideanGeometry

abbrev Point : Type := ℝ^2


/-
`numberOfConvexSubsets S hS` counts all subsets of `S` that are in convex
position (`ConvexIndependent`).
-/
noncomputable def numberOfConvexSubsets (S : Set Point) (hS : S.Finite) : ℕ :=
  {A ⊆ S | ConvexIndependent ℝ (fun x : A => (x : Point))}.ncard

/-
`f n` is the minimum number of convex subsets determined by any set of `n` points
in general position.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf
    { k : ℕ |
      ∃ S : Set Point, ∃ hS : S.Finite,
        S.ncard = n ∧ GeneralPosition (R := ℝ) S ∧
        numberOfConvexSubsets S hS = k }

/-
There exists a constant $c$ such that $\lim_{n \to \infty} \frac{\log f(n)}{(\log n)^2} = c$.
-/
@[category research open, AMS 52]
theorem erdos_838 :
    ∃ c : ℝ,
      Filter.Tendsto
        (fun n => Real.log (f n) / (Real.log n)^2)
        Filter.atTop (nhds c) := by
  sorry

end Erdos838
