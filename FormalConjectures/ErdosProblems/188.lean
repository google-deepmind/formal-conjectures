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
# Erdős Problem 188

*Reference:* [erdosproblems.com/188](https://www.erdosproblems.com/188)
-/

namespace Erdos188

/--
The set of numbers $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1.
-/
def s := { k : ℕ | ∃ blue : Set ℂ,
    (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) ∧
    ¬ (∃ bs ⊆ blue, (∃ s, bs.IsAPOfLengthWith k s 1)) }

/--
Old and new problems and results in combinatorial number theory by Erdős & Graham (Page 14, 15):

It has been shown that there is a large $M$ so that it is possible to partition $\mathbb{E}^2$ into
two sets $A$ and $B$ so that $A$ contains no pair of points with distance 1 and $B$ contains no A.P.
of length $M$.
-/
@[category research solved, AMS 5]
theorem erdos_188.nonempty : s.Nonempty := by
  sorry

/--
Old and new problems and results in combinatorial number theory by Erdős & Graham (Page 15):

How small can $M$ be made? The only estimate currently known is that $M$ ≤ 10000000 (more or less).
In the other direction, it has just been shown by R. Juhász [Ju (79)] that we must have $M$ ≥ 5.
-/
@[category research solved, AMS 5]
theorem erdos_188.estimate : (∀ k, k ∈ s → 5 ≤ k) ∧ (∃ k ∈ s, k ≤ 10000000) := by
  sorry

/--
What is the smallest $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1?
-/
@[category research open, AMS 5]
theorem erdos_188 : IsLeast s answer(sorry) := by
  sorry

end Erdos188
