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
# Erdős Problem 650

*Reference:* [erdosproblems.com/650](https://www.erdosproblems.com/650)

Let `f(m)` be such that, whenever `A ⊆ {1, ..., N}` has `|A| = m`, every
interval of length `2N` contains at least `f(m)` distinct integers
`b₁, ..., b_r`, each divisible by a distinct element of `A`.  Estimate `f(m)`.
-/

noncomputable section

namespace Erdos650

open Classical

/--
Inside the interval `[x, x + 2N - 1]`, the set `B` is witnessed by an injective
assignment of distinct divisors from `A`.
-/
def IntervalHasDivisibleWitnesses (A : Finset ℕ) (N x r : ℕ) : Prop :=
  ∃ B : Finset ℕ,
    r ≤ B.card ∧
      B ⊆ Finset.Icc x (x + 2 * N - 1) ∧
        ∃ divisorOf : ℕ → ℕ,
          (∀ b : ℕ, b ∈ B → divisorOf b ∈ A ∧ divisorOf b ∣ b) ∧
            Set.InjOn divisorOf {b : ℕ | b ∈ B}

/-- `r` is guaranteed for every `m`-element subset of `{1, ..., N}`. -/
def GuaranteedDivisibleWitnessCount (m r : ℕ) : Prop :=
  ∀ N : ℕ,
    ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
        A.card = m →
          ∀ x : ℕ, 1 ≤ x → IntervalHasDivisibleWitnesses A N x r

/-- `f m` is the greatest universally guaranteed witness count. -/
def IsFValue (m f : ℕ) : Prop :=
  IsGreatest {r : ℕ | GuaranteedDivisibleWitnessCount m r} f

/-- A function equal to the extremal function `f(m)`. -/
def Erdos650Function (f : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, IsFValue m (f m)

/-- Determine the extremal function `f(m)`. -/
@[category research solved, AMS 11]
theorem erdos_650 : {f : ℕ → ℕ | Erdos650Function f} = answer(sorry) := by
  sorry

end Erdos650

end
