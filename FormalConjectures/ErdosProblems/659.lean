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
# Erdős Problem 659

*Reference:* [erdosproblems.com/659](https://www.erdosproblems.com/659)
-/

open EuclideanGeometry Finset

namespace Erdos659

noncomputable def minimalDistinctDistancesSubsetOfSize (points : Set ℝ²) (n : ℕ) : ℕ :=
  sInf {(distinctDistances subset : ℝ) |
    (subset : Finset ℝ²) (_ : subset.toSet ⊆ points) (_ : subset.card = n)}

/--
Is there a set of $n$ points in $\mathbb{R}^2$ such that every subset of $4$ points determines at
least $3$ distances, yet the total number of distinct distances is \ll \frac{n}{\sqrt{\log n}}?
-/
@[category research open, AMS 52]
theorem erdos_659 : (∃ (a : ℕ → Finset ℝ²), ∀ n, #(a n) = n ∧
    3 ≤ minimalDistinctDistancesSubsetOfSize (a n) 4 ∧
    (fun n => (distinctDistances (a n) : ℝ)) ≪ fun (n : ℕ) => n /(n : ℝ).log.sqrt)
    ↔ answer(sorry) := by
  sorry


end Erdos659
