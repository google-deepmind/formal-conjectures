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
# Erdős Problem 711

*Reference:* [erdosproblems.com/711](https://www.erdosproblems.com/711)

Let `f(n,m)` be minimal such that in `(m, m + f(n,m))` there exist distinct
integers `a₁, ..., a_n` such that `k ∣ a_k` for all `1 ≤ k ≤ n`.  The problem
asks to prove `max_m f(n,m) ≤ n^{1 + o(1)}` and
`max_m (f(n,m) - f(n,n)) → ∞`.
-/

noncomputable section

namespace Erdos711

open Classical Filter Asymptotics

/--
There are distinct `a_1, ..., a_n` in the open interval `(m, m + L)` such that
`(i + 1)` divides the point indexed by `i : Fin n`.
-/
def HasDivisibleDistinctTuple (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ,
    Function.Injective a ∧
      ∀ i : Fin n, m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

/-- `L` is the minimal interval length for the parameters `(n,m)`. -/
def IsMinimalIntervalLength (n m L : ℕ) : Prop :=
  HasDivisibleDistinctTuple n m L ∧
    ∀ L' : ℕ, HasDivisibleDistinctTuple n m L' → L ≤ L'

/-- The uniform upper bound `max_m f(n,m) ≤ n^{1+o(1)}`. -/
def Erdos711UpperBoundConjecture : Prop :=
  ∃ error : ℕ → ℝ,
    error =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ n in atTop,
        ∀ m : ℕ,
          ∃ L : ℕ,
            HasDivisibleDistinctTuple n m L ∧
              (L : ℝ) ≤ Real.rpow (n : ℝ) (1 + error n)

/-- The assertion `max_m (f(n,m) - f(n,n)) → ∞`. -/
def Erdos711UnboundedDifferenceConjecture : Prop :=
  ∀ B : ℕ,
    ∀ᶠ n in atTop,
      ∃ m Lm Ln : ℕ,
        IsMinimalIntervalLength n m Lm ∧
          IsMinimalIntervalLength n n Ln ∧
            B ≤ Lm - Ln

/-- Prove `max_m f(n,m) ≤ n^{1+o(1)}`. -/
@[category research open, AMS 11]
theorem erdos_711.parts.i : answer(sorry) ↔ Erdos711UpperBoundConjecture := by
  sorry

/-- Prove `max_m (f(n,m) - f(n,n)) → ∞`. -/
@[category research open, AMS 11]
theorem erdos_711.parts.ii :
    answer(sorry) ↔ Erdos711UnboundedDifferenceConjecture := by
  sorry

end Erdos711

end

