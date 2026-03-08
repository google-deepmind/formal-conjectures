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
# Erdős Problem 153

#TODO: Formalize the corresponding conjecture for infinite Sidon sets.

*References:*
 - [erdosproblems.com/153](https://www.erdosproblems.com/153)
 - [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
    Theory (1994), 329-347.
-/

open scoped Pointwise
open Filter Finset Nat

namespace Erdos153

/-- Define `f n` to be the minimum of
`∑ (i : Set.Ico 1 ((A + A).card), (s i - s (i - 1)) ^ 2 / n` as `A` ranges over all Sidon sets
of size `n`, where `s` is an order embedding from `Fin n` into `A`. -/
noncomputable def f (n : ℕ) : ℝ := ⨅ A : {A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)},
  let s := (A.1 + A).orderIsoOfFin rfl
  ∑ i : Set.Ico 1 ((A.1 + A).card), (s ⟨i, i.2.2⟩ - s ⟨i - 1, by grind⟩) ^ 2 / (n : ℝ)

/-- Must `lim f n = ∞`? -/
@[category research open, AMS 5]
theorem erdos_153 : answer(sorry) ↔ Tendsto f atTop atTop := by
  sorry

end Erdos153
