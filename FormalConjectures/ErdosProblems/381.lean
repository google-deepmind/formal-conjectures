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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 381

*References:*
- [erdosproblems.com/381](https://www.erdosproblems.com/381)
-/

@[expose] public section

open Filter Topology MeasureTheory SimpleGraph

namespace Erdos381

/-- A positive integer has more divisors than every smaller positive integer. -/
def HighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → m.divisors.card < n.divisors.card

/-- The counting function of highly composite numbers. -/
noncomputable def Q (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter HighlyComposite).card

/-- Is $Q(x) \gg_k (\log x)^k$ for every $k\geq 1$? Nicolas [Ni71] disproved this. -/
@[category research solved, question, AMS 11]
theorem erdos_381 :
    ¬ (∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c * (Real.log x) ^ k ≤ (Q x : ℝ)) := by
  sorry

end Erdos381
