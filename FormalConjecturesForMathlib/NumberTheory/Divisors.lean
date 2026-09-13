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
public import Mathlib.Data.Real.Basic
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

/-- The ratio `d_{i+1}/d_i` of consecutive divisors of `n` in increasing order (0-indexed).

Takes a junk value if `i + 1` is not a valid index in `n.divisors`. -/
noncomputable def consecutiveDivisorRatio (n i : ℕ) : ℝ :=
  (nth (· ∈ n.divisors) (i + 1) : ℝ) / nth (· ∈ n.divisors) i

/-- The first consecutive ratio is just `d_2`, since `d_1 = 1`. -/
lemma consecutiveDivisorRatio_zero {n : ℕ} (hn : n ≠ 0) :
    consecutiveDivisorRatio n 0 = (nth (· ∈ n.divisors) 1 : ℝ) := by
  rw [consecutiveDivisorRatio, nth_divisors_zero hn, Nat.cast_one, div_one]

/-- Every divisor enumerated after index `0` is at least `2`. -/
lemma two_le_nth_divisors {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i ≠ 0)
    (h : Nat.nth (· ∈ n.divisors) i ≠ 0) : 2 ≤ Nat.nth (· ∈ n.divisors) i := by
  have hfin : (Set.ofPred (· ∈ n.divisors)).Finite := n.divisors.finite_toSet
  have hpos : 1 ≤ Nat.nth (· ∈ n.divisors) i := Nat.pos_of_mem_divisors (Nat.nth_mem_of_ne_zero h)
  rcases hpos.lt_or_eq with h2 | h1
  · omega
  · exact absurd (Nat.nth_injOn hfin
      (Set.mem_Iio.mpr (Nat.lt_card_toFinset_of_nth_ne_zero h hfin))
      (Set.mem_Iio.mpr (Nat.lt_card_toFinset_of_nth_ne_zero
        (show Nat.nth (· ∈ n.divisors) 0 ≠ 0 by rw [nth_divisors_zero hn]; omega) hfin))
      (by rw [nth_divisors_zero hn]; omega)) hi

/-- Consecutive ratios are at least `1` when the earlier divisor is positive and strictly
smaller than the next. -/
lemma one_le_consecutiveDivisorRatio_of_lt {n i : ℕ}
    (hpos : 0 < nth (· ∈ n.divisors) i)
    (h : nth (· ∈ n.divisors) i < nth (· ∈ n.divisors) (i + 1)) :
    (1 : ℝ) ≤ consecutiveDivisorRatio n i := by
  have hposR : (0 : ℝ) < nth (· ∈ n.divisors) i := Nat.cast_pos.mpr hpos
  rw [consecutiveDivisorRatio, le_div_iff₀ hposR, one_mul]
  exact_mod_cast h.le

/-- On valid indices (`i + 1 < τ(n)`), consecutive divisor ratios are ≥ `1`. -/
lemma one_le_consecutiveDivisorRatio {n i : ℕ}
    (hi : i + 1 < n.divisors.card) :
    (1 : ℝ) ≤ consecutiveDivisorRatio n i := by
  classical
  have hfin : (Set.ofPred (· ∈ n.divisors)).Finite := n.divisors.finite_toSet
  have hcard : hfin.toFinset.card = n.divisors.card := by
    congr 1
    ext x
    simp [Set.Finite.mem_toFinset]
  have hlt := nth_lt_nth_of_lt_card hfin (Nat.lt_succ_self i) (by rw [hcard]; exact hi)
  have hpos : 0 < nth (· ∈ n.divisors) i :=
    Nat.pos_of_mem_divisors (nth_mem_of_lt_card hfin (lt_trans (Nat.lt_succ_self i) (by rw [hcard]; exact hi)))
  exact one_le_consecutiveDivisorRatio_of_lt hpos hlt

end Nat
