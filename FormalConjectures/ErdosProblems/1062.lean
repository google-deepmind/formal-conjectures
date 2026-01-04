/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1062

*Reference:* [erdosproblems.com/1062](https://www.erdosproblems.com/1062)
-/

open Classical Filter

namespace Erdos1062

/-- A finite set `A` of positive integers is fork-free if no element divides
two distinct other elements of `A`. -/
def ForkFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, {b ∈ A \ {a} | a ∣ b}.Subsingleton

/-- `Admissible A n` means that `A` is contained in `{1,...,n}` and is fork-free. -/
def Admissible (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ ForkFree A

/-- The extremal function from Erdős problem 1062: the largest size of a fork-free subset of
`{1,...,n}`. -/
def f (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∃ A, Admissible A n ∧ A.card = k) n

/-- The interval `[m + 1, 3m + 2]` gives a construction showing that `f n` is asymptotically
at least `2n / 3`. -/
@[category research open, AMS 11]
theorem erdos_1062.lower_bound (n : ℕ) : ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n := by
  sorry

/-- Lebensold proved that for large `n`, the function `f n` lies between `0.6725 n` and
`0.6736 n`. -/
@[category research solved, AMS 11]
theorem erdos_1062.lebensold_bounds :
    ∃ N, ∀ ⦃n⦄, N ≤ n →
      (0.6725 : ℝ) * n ≤ f n ∧ f n ≤ (0.6736 : ℝ) * n := by
  sorry

/-- Erdős asked whether the limiting density `f n / n` exists and, if so, whether it is
irrational. -/
@[category research open, AMS 11]
theorem erdos_1062.limit_density :
    (∃ l, Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 l) ∧ Irrational l) ↔ answer(sorry) := by
  sorry

end Erdos1062
