/-
Copyright 2025 The Formal Conjectures Authors
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
# Erdős Problem 312 — Fintype Formulation

*Reference:* https://www.erdosproblems.com/312

We state a version of the problem using functions `Fin n → ℕ` to represent a
finite indexed family of positive integers and `Finset (Fin n)` for chosen
subsets, making multiplicities explicit by indexing with `Fin n`.
-/

open scoped BigOperators
open Filter

namespace Erdos312

noncomputable section

variable {n : ℕ}

/-- A short name for a finite family of (nonnegative) integers indexed by `Fin n`. -/
abbrev Family (n : ℕ) := Fin n → ℕ

/-- Harmonic sum of the entries of `a` over the index set `S`. -/
def hsumIdx (a : Family n) (S : Finset (Fin n)) : ℝ :=
  ∑ i in S, (1 : ℝ) / (a i : ℝ)

/-!
## A placeholder formulation

Replace the statement below by your preferred precise version.
Keeping a compiling skeleton helps other files build while you iterate.
-/

/-- (Placeholder) One possible finite formulation related to Erdős 312.
Fill in the exact hypotheses and conclusion you want; the proof can remain `sorry`. -/
theorem erdos312_placeholder
    (a : Family n) :
    True := by
  trivial

/-- (Optional helper) Selecting a nonempty subset with some property.
Sketch lemma you might need; keep as a stub for now. -/
lemma exists_subset_with_property
    (a : Family n) :
    ∃ S : Finset (Fin n), True := by
  refine ⟨∅, ?_⟩
  trivial

end  -- closes `noncomputable section`

end Erdos312
