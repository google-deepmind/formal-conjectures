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

module

public import FormalConjecturesUtil

/-!
# Ore's harmonic numbers

A001599 lists the positive integers whose positive divisors have an integral harmonic mean.
Equivalently, $n$ belongs to the sequence when
$\sigma_1(n) \mid n\sigma_0(n)$, where $\sigma_1(n)$ is the sum of the divisors of $n$ and
$\sigma_0(n)$ is their number.

*References:*
- [A001599](https://oeis.org/A001599)
-/

@[expose] public section

namespace OeisA1599

open scoped ArithmeticFunction.sigma

/-- A positive integer $n$ belongs to A001599 when
$\sigma_1(n) \mid n\sigma_0(n)$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n ∣ n * σ 0 n

@[category test, AMS 11]
theorem not_a_0 : ¬ A 0 := by
  simp [A]

@[category test, AMS 11]
theorem not_a_2 : ¬ A 2 := by
  unfold A
  decide

@[category test, AMS 11]
theorem not_a_3 : ¬ A 3 := by
  unfold A
  decide

@[category test, AMS 11]
theorem a_1 : A 1 := by
  refine ⟨by norm_num, ?_⟩
  decide

@[category test, AMS 11]
theorem a_6 : A 6 := by
  refine ⟨by norm_num, ?_⟩
  decide

@[category test, AMS 11]
theorem a_28 : A 28 := by
  refine ⟨by norm_num, ?_⟩
  decide

@[category test, AMS 11]
theorem a_140 : A 140 := by
  refine ⟨by norm_num, ?_⟩
  decide

@[category test, AMS 11]
theorem a_270 : A 270 := by
  refine ⟨by norm_num, ?_⟩
  decide

/--
"Ore conjectured that 1 is the only odd harmonic number."

*Reference:* [A001599](https://oeis.org/A001599)
-/
@[category research open, AMS 11]
theorem eq_one_of_odd_of_a {n : ℕ} (hn : A n) (hodd : Odd n) : n = 1 := by
  sorry

end OeisA1599
