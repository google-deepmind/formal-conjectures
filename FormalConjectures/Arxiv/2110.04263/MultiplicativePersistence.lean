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
# Multiplicative persistence

Multiply the decimal digits of a natural number, then repeat. The multiplicative-persistence
conjecture says that a single digit is always reached in at most eleven steps.

*References:*
* Eric Brier, Christophe Clavier, Linda Gutsche, and David Naccache,
  [*The Multiplicative Persistence Conjecture Is True for Odd Targets*](
  https://arxiv.org/abs/2110.04263)
* [OEIS A003001](https://oeis.org/A003001)
-/

@[expose] public section

namespace Arxiv.«2110.04263»

/-- The product of the base-ten digits of a natural number, with zero mapped to zero. -/
def digitProduct : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Nat.digits 10 (n + 1)).prod

/-- The explicit zero convention makes zero a fixed point of the digit-product map. -/
@[category test, AMS 11]
theorem digitProduct_zero : digitProduct 0 = 0 := by
  rfl

/-- Every single decimal digit is a fixed point of the digit-product map. -/
@[category test, AMS 11]
theorem digit_product_eq_of_lt_ten {n : ℕ} (hn : n < 10) : digitProduct n = n := by
  interval_cases n <;> norm_num [digitProduct]

/-- A single-digit starting value satisfies the conjectured bound with zero iterations. -/
@[category test, AMS 11]
theorem single_digit_zero_iterations {n : ℕ} (hn : n < 10) :
    ∃ k ≤ 11, (digitProduct^[k]) n < 10 := by
  exact ⟨0, by norm_num, by simpa using hn⟩

/-- The first three steps from $39$ are $39\mapsto27\mapsto14\mapsto4$. -/
@[category test, AMS 11]
theorem trajectory_39 :
    digitProduct 39 = 27 ∧ digitProduct 27 = 14 ∧ digitProduct 14 = 4 := by
  norm_num [digitProduct]

/-- Three applications of the digit-product map take $39$ to the single digit $4$. -/
@[category test, AMS 11]
theorem iterate_three_39 : (digitProduct^[3]) 39 = 4 := by
  norm_num [Function.iterate_succ_apply, digitProduct]

/-- After ten steps, the standard persistence-eleven example has reached $20$. -/
@[category test, AMS 11]
theorem iterate_ten_277777788888899 :
    (digitProduct^[10]) 277777788888899 = 20 := by
  norm_num [Function.iterate_succ_apply, digitProduct]

/-- The eleventh step takes the standard persistence-eleven example from $20$ to $0$. -/
@[category test, AMS 11]
theorem iterate_eleven_277777788888899 :
    (digitProduct^[11]) 277777788888899 = 0 := by
  norm_num [Function.iterate_succ_apply, digitProduct]

/-- No iterate before step eleven has reached a single digit for the standard sharpness example. -/
@[category test, AMS 11]
theorem persistence_eleven_lower_bound :
    ∀ k < 11, 10 ≤ (digitProduct^[k]) 277777788888899 := by
  intro k hk
  interval_cases k <;>
    norm_num [Function.iterate_succ_apply, digitProduct]

/--
The multiplicative-persistence conjecture: every natural number reaches a single decimal digit
after at most eleven iterations of the digit-product map.

The bound is sharp: $277777788888899$ has multiplicative persistence eleven.

*Reference:* [arXiv:2110.04263](https://arxiv.org/abs/2110.04263)
-/
@[category research open, AMS 11]
theorem multiplicative_persistence_conjecture :
    ∀ n : ℕ, ∃ k ≤ 11, (digitProduct^[k]) n < 10 := by
  sorry

end Arxiv.«2110.04263»
