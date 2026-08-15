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
# Erdős Problem 462

*Reference:* [erdosproblems.com/462](https://www.erdosproblems.com/462)

Let `p(n)` denote the least prime factor of `n`.  Is there a constant `C > 0`
such that
`∑_{x ≤ n ≤ x + C x^(1/2) (log x)^2} p(n) / n ≫ 1`
for all sufficiently large `x`?
-/

noncomputable section

namespace Erdos462

open Classical Filter
open scoped BigOperators

/-- `p` is the least prime factor of `n`. -/
def LeastPrimeFactor (n p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ n ∧ ∀ q : ℕ, Nat.Prime q → q ∣ n → p ≤ q

/-- `p` chooses a least prime factor for every integer greater than `1`. -/
def LeastPrimeFactorChoice (p : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 < n → LeastPrimeFactor n (p n)

/-- The summand `p(n) / n`, after choosing least prime factors. -/
def leastPrimeFactorTerm (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  (p n : ℝ) / (n : ℝ)

/-- `y` is the least natural endpoint not below `x + C sqrt x (log x)^2`. -/
def IsCeilingShortIntervalEndpoint (C : ℝ) (x y : ℕ) : Prop :=
  (x : ℝ) + C * Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ 2 ≤ (y : ℝ) ∧
    ∀ z : ℕ,
      (x : ℝ) + C * Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ 2 ≤ (z : ℝ) →
        y ≤ z

/-- The short-interval lower-bound conjecture from Erdős problem 462. -/
def Erdos462Conjecture : Prop :=
  ∃ C c : ℝ,
    0 < C ∧
      0 < c ∧
        ∀ p : ℕ → ℕ,
          LeastPrimeFactorChoice p →
            ∀ᶠ x in atTop,
              ∃ y : ℕ,
                IsCeilingShortIntervalEndpoint C x y ∧
                  c ≤ (Finset.Icc x y).sum fun n => leastPrimeFactorTerm p n

/--
Is there a constant `C > 0` such that every sufficiently large interval
`[x, x + C x^(1/2) (log x)^2]` carries bounded-below mass from `p(n) / n`?
-/
@[category research open, AMS 11]
theorem erdos_462 : answer(sorry) ↔ Erdos462Conjecture := by
  sorry

end Erdos462

end
