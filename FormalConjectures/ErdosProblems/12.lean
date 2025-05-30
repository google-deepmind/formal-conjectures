/-
Copyright 2025 Google LLC

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
# Erdős Problem 12

*Reference:* [erdosproblems.com/12](https://www.erdosproblems.com/12)
-/

open Classical

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c∈A`
such that `a∣(b+c)` and `b,c>a`.
-/
abbrev good (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

/--
Let `A` be an infinite set such that there are no distinct `a,b,c ∈ A`
such that `a∣(b+c)` and `b,c > a`. Is there such an `A` with
`lim inf |A ∩ {1,…,N}| / N^(1/2) > 0` ?
Does there exist some absolute constant `c > 0`
such that there are always infinitely many `N`
with `|A ∩ {1,…,N}|< N^(1−c)`?
Is it true that `∑ n ∈ A, 1 / n < ∞`?
-/
theorem erdos_12.parts.i : ∃ (A : Set ℕ), good A ∧
    (0 : ℝ) < Filter.atTop.liminf
      (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ).sqrt) := by
  sorry


theorem erdos_12.parts.ii : ∃ (A : Set ℕ), good A ∧
    (0 : ℝ) < Filter.atTop.liminf
      (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ).sqrt) := by
  sorry

/-- Erdős and Sárközy proved that such an $A$ must have density 0. -/
theorem erdos_12.variants.density_0
    (A : Set ℕ) (hA : good A) : Set.HasDensity 0 := by
  sorry
