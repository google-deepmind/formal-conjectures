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
# Erdős Problem 663

*Reference:* [erdosproblems.com/663](https://www.erdosproblems.com/663)

Let `q(n,k)` denote the least prime which does not divide
`∏_{1 ≤ i ≤ k} (n + i)`.  The problem asks whether, for fixed `k` and
sufficiently large `n`, one has `q(n,k) < (1 + o(1)) log n`.
-/

noncomputable section

namespace Erdos663

open Classical Filter Asymptotics
open scoped BigOperators

/-- The product `(n + 1) * ... * (n + k)`. -/
def intervalProduct (n k : ℕ) : ℕ :=
  (Finset.Icc 1 k).prod fun i => n + i

/-- `q` is the least prime not dividing `(n + 1) * ... * (n + k)`. -/
def IsLeastPrimeNotDividingIntervalProduct (n k q : ℕ) : Prop :=
  Nat.Prime q ∧
    ¬ q ∣ intervalProduct n k ∧
      ∀ p : ℕ, Nat.Prime p → ¬ p ∣ intervalProduct n k → q ≤ p

/--
The assertion `q(n,k) < (1 + o(1)) log n`, with the `o(1)` term represented by
an explicit error function depending on `k`.
-/
def Erdos663Conjecture : Prop :=
  ∀ k : ℕ,
    1 ≤ k →
      ∃ error : ℕ → ℝ,
        error =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
          ∀ᶠ n in atTop,
            ∃ q : ℕ,
              IsLeastPrimeNotDividingIntervalProduct n k q ∧
                (q : ℝ) < (1 + error n) * Real.log (n : ℝ)

/--
For fixed `k`, is the least prime not dividing `(n + 1) * ... * (n + k)` less
than `(1 + o(1)) log n`?
-/
@[category research open, AMS 11]
theorem erdos_663 : answer(sorry) ↔ Erdos663Conjecture := by
  sorry

end Erdos663

end

