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
# Erdős Problem 433

*Reference:* [erdosproblems.com/433](https://www.erdosproblems.com/433)

For a finite set `A ⊂ ℕ`, let `G(A)` be the greatest integer not expressible as
a finite sum of elements of `A`, repetitions allowed.  Let `g(k,n)` be the
maximum of `G(A)` over `k`-element subsets `A ⊆ {1, ..., n}` with no common
divisor.  Is `g(k,n) ~ n^2 / (k - 1)`?
-/

noncomputable section

namespace Erdos433

open Classical Filter
open scoped Topology
open scoped BigOperators

/-- `m` is representable as a finite sum of elements of `A`, with repetitions. -/
def RepresentableByFiniteSums (A : Finset ℕ) (m : ℕ) : Prop :=
  ∃ coeff : ℕ → ℕ,
    (∀ a : ℕ, coeff a ≠ 0 → a ∈ A) ∧
      m = A.sum fun a => coeff a * a

/-- The elements of `A` have no common divisor greater than `1`. -/
def HasNoCommonDivisor (A : Finset ℕ) : Prop :=
  ∀ d : ℕ, (∀ a : ℕ, a ∈ A → d ∣ a) → d = 1

/-- `G` is the greatest integer not representable as a finite sum from `A`. -/
def IsFrobeniusValue (A : Finset ℕ) (G : ℕ) : Prop :=
  IsGreatest {m : ℕ | ¬ RepresentableByFiniteSums A m} G

/-- `g` is the extremal Frobenius value `g(k,n)`. -/
def IsGValue (k n g : ℕ) : Prop :=
  IsGreatest
    {G : ℕ |
      ∃ A : Finset ℕ,
        A ⊆ Finset.Icc 1 n ∧
          A.card = k ∧
            HasNoCommonDivisor A ∧
              IsFrobeniusValue A G}
    g

/-- A chosen function equal to `g(k,n)` for fixed `k`. -/
def GFunctionForK (k : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, IsGValue k n (g n)

/-- The asymptotic statement `g(k,n) ~ n^2 / (k - 1)` for fixed `k`. -/
def Erdos433Asymptotic : Prop :=
  ∀ k : ℕ,
    2 ≤ k →
      ∃ g : ℕ → ℕ,
        GFunctionForK k g ∧
          Tendsto
            (fun n : ℕ => (g n : ℝ) / ((n : ℝ) ^ 2 / ((k : ℝ) - 1)))
            atTop
            (𝓝 1)

/-- Is `g(k,n) ~ n^2 / (k - 1)` for fixed `k`? -/
@[category research solved, AMS 11]
theorem erdos_433 : answer(True) ↔ Erdos433Asymptotic := by
  sorry

end Erdos433

end
