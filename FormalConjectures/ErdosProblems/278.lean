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
public import FormalConjecturesForMathlib.NumberTheory.CongruenceCovering

/-!
# Erdős Problem 278: minimum covered density

*Reference:* [erdosproblems.com/278](https://www.erdosproblems.com/278)

This file formalizes the settled minimum-density question. The maximum-density question
remains open and is not included here.
-/

@[expose] public section

open scoped Classical

namespace Erdos278

open CongruenceCovering

variable {ι : Type*} [Fintype ι]

/-- The natural density of a finite union of residue classes is minimized when all residues
are equal. Its minimum is the inclusion–exclusion sum of the reciprocals of the least common
multiples. This is the second question of Erdős Problem 278, settled by Rogers and Simpson. -/
@[category research solved, AMS 11]
theorem erdos_278_min (n : ι → ℕ) (hn : ∀ i, 0 < n i) :
    ∃ δ : (ι → ℤ) → ℝ,
      (∀ a, HasNatDensity {x : ℕ | Covered n a x} (δ a)) ∧
      (∀ a, δ 0 ≤ δ a) ∧
      (∀ c : ℤ, δ (fun _ => c) = δ 0) ∧
      δ 0 = ∑ t ∈ (Finset.univ : Finset ι).powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (t.card + 1) / ((t.lcm n : ℕ) : ℝ) := by
  exact rogers_min_density n hn

end Erdos278
