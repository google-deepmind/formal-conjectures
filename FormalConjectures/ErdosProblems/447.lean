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
# Erdős Problem 447

*Reference:* [erdosproblems.com/447](https://www.erdosproblems.com/447)

How large can a union-free family of subsets of `[n]` be?  A family is
union-free if there are no distinct `A, B, C` in the family with `A ∪ B = C`.
The sharpened bound asks whether the maximum is less than
`(1 + o(1)) * binom(n, floor(n/2))`.
-/

noncomputable section

namespace Erdos447

open Classical Filter
open scoped Topology

/-- A family of subsets of `Fin n` is union-free. -/
def UnionFree {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃A B C : Finset (Fin n)⦄,
    A ∈ F →
      B ∈ F →
        C ∈ F →
          A ≠ B →
            A ≠ C →
              B ≠ C →
                A ∪ B = C → False

/-- `m` is the maximum size of a union-free family on `[n]`. -/
def IsUnionFreeExtremalValue (n m : ℕ) : Prop :=
  IsGreatest
    {s : ℕ | ∃ F : Finset (Finset (Fin n)), UnionFree F ∧ F.card = s}
    m

/-- A chosen extremal function for union-free families. -/
def UnionFreeExtremalFunction (M : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, IsUnionFreeExtremalValue n (M n)

/-- The solved asymptotic upper bound of Kleitman. -/
def Erdos447StrongAsymptotic : Prop :=
  ∃ M : ℕ → ℕ,
    UnionFreeExtremalFunction M ∧
      (∀ ε : ℝ,
        0 < ε →
          ∀ᶠ n in atTop,
            (M n : ℝ) ≤ (1 + ε) * (Nat.choose n (n / 2) : ℝ)) ∧
        Tendsto (fun n : ℕ => (M n : ℝ) / (2 ^ n : ℝ)) atTop (𝓝 0)

/-- Formalized statement of the union-free-family extremal bound. -/
@[category research solved, AMS 5]
theorem erdos_447 : answer(True) ↔ Erdos447StrongAsymptotic := by
  sorry

end Erdos447

end
