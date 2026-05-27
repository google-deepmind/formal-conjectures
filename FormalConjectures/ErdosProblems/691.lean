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
# Erdős Problem 691

*Reference:* [erdosproblems.com/691](https://www.erdosproblems.com/691)

Given `A ⊆ ℕ`, let `M_A = {n ≥ 1 : a ∣ n` for some `a ∈ A}` be the set of
multiples of `A`.  Find a necessary and sufficient condition on `A` for `M_A`
to have density `1`.
-/

noncomputable section

namespace Erdos691

open Classical Filter
open scoped Topology

/-- The set of positive multiples of a set `A` of natural numbers. -/
def MultiplesOfSet (A : Set ℕ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ a : ℕ, a ∈ A ∧ a ∣ n

/-- Natural density of a predicate on the positive integers. -/
def HasNaturalDensity (P : ℕ → Prop) (d : ℝ) : Prop :=
  Tendsto
    (fun N : ℕ => by
      classical
      exact (((Finset.Icc 1 N).filter fun n => P n).card : ℝ) / (N : ℝ))
    atTop
    (𝓝 d)

/-- The property that `A` is a Behrend sequence, i.e. its multiples have density `1`. -/
def MultiplesHaveDensityOne (A : Set ℕ) : Prop :=
  HasNaturalDensity (MultiplesOfSet A) 1

/-- A proposed necessary and sufficient condition for `M_A` to have density `1`. -/
def CharacterizesDensityOneMultiples (C : Set ℕ → Prop) : Prop :=
  ∀ A : Set ℕ, C A ↔ MultiplesHaveDensityOne A

/--
Determine a necessary and sufficient condition on `A` for the set of multiples
of `A` to have natural density `1`.
-/
@[category research open, AMS 11]
theorem erdos_691 :
    {C : Set ℕ → Prop | CharacterizesDensityOneMultiples C} = answer(sorry) := by
  sorry

end Erdos691

end
