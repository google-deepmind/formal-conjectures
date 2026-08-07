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

public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Divisors

@[expose] public section

/-!
# The increasing enumeration of the divisors of a natural number

Basic facts about `Nat.nth (· ∈ n.divisors)`, the increasing enumeration of the divisors of `n`.
-/

namespace Nat

/-- The smallest divisor of a positive number is `1`, i.e. the `0`th entry of the increasing
enumeration of its divisors. -/
lemma nth_divisors_zero {n : ℕ} (hn : n ≠ 0) : Nat.nth (· ∈ n.divisors) 0 = 1 := by
  rw [Nat.nth_zero]
  exact IsLeast.csInf_eq ⟨Nat.one_mem_divisors.mpr hn, fun y hy => Nat.pos_of_mem_divisors hy⟩

/-- Every divisor enumerated after index `0` is at least `2`. -/
lemma two_le_nth_divisors {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i ≠ 0)
    (h : Nat.nth (· ∈ n.divisors) i ≠ 0) : 2 ≤ Nat.nth (· ∈ n.divisors) i := by
  have hfin : (setOf (· ∈ n.divisors)).Finite := Set.toFinite _
  have hpos : 1 ≤ Nat.nth (· ∈ n.divisors) i := Nat.pos_of_mem_divisors (Nat.nth_mem_of_ne_zero h)
  rcases hpos.lt_or_eq with h2 | h1
  · omega
  · exact absurd (Nat.nth_injOn hfin
      (Set.mem_Iio.mpr (Nat.lt_card_toFinset_of_nth_ne_zero h hfin))
      (Set.mem_Iio.mpr (Nat.lt_card_toFinset_of_nth_ne_zero
        (show Nat.nth (· ∈ n.divisors) 0 ≠ 0 by rw [nth_divisors_zero hn]; omega) hfin))
      (by rw [nth_divisors_zero hn]; omega)) hi

end Nat
