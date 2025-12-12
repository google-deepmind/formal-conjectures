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
# Erdős Problem 1101

*Reference:* [erdosproblems.com/1101](https://www.erdosproblems.com/1101)
-/

open Nat Filter

namespace Erdos1101

/-- The set of integers not divisible by any u_i. -/
def ASet (u : ℕ → ℕ) : Set ℕ :=
  { a | ∀ i, ¬ u i ∣ a }

/-- The sequence of integers A_u which are not divisible by any u_i
arranged in a monotonic sequence. -/
noncomputable def A (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun a => a ∈ ASet u) n

/-- t_x such that u_0 ... u_{t_x-1} ≤ x < u_0 ... u_{t_x}.
-/
noncomputable def t (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  sSup { k | ∏ i ∈ Finset.range k, u i ≤ x }

/-- A sequence is "good" if
1. it is strictly monotone
2. it is pairwise coprime
3. the sum of reciprocals converges
4. the gap between consecutive elements in A(u) is bounded relative to t_x. -/
def IsGood (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧
  (∀ i j, i ≠ j → Coprime (u i) (u j)) ∧
  Summable (fun n => 1 / (u n : ℝ)) ∧
  ∀ ε > 0, ∀ᶠ x in atTop,
    ∀ k, A u k < x →
      (A u (k + 1) : ℝ) - A u k < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹

/-- 1. There is NO good sequence with polynomial growth. -/
@[category research open, AMS 11]
theorem erdos_1101.polynomial : ¬ ∃ u, IsGood u ∧ ∃ k : ℕ, (fun n => (u n : ℝ)) =O[atTop] (fun n => (n : ℝ) ^ k) :=
  sorry

/-- 2. There is a good sequence with sub-exponential growth. -/
@[category research open, AMS 11]
theorem erdos_1101.subexponential : ∃ u, IsGood u ∧ ∀ (ε : ℝ), 0 < ε → (fun n => (u n : ℝ)) =o[atTop] (fun n => Real.exp (ε * n)) :=
  sorry

end Erdos1101
