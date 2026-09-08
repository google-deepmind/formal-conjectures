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
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Basic

/-!
# Integer powers of a group element

Two facts about `zpow` that Mathlib does not state in this form.

## Main results

* `zpow_sum_eq_prod`: an integer power with a summed exponent is a product of powers.
  This is the `zpow` analogue of `pow_add`, indexed by a `Finset`; Mathlib's `Finset.prod_zpow`
  distributes a *fixed* exponent over a product instead.
* `zpow_eq_zpow_of_pow_eq_one`: exponents congruent modulo `k` give the same power of an element
  killed by `k`. Mathlib's `zpow_eq_zpow_iff_modEq` is the sharp version with `orderOf x`, which
  needs the order to be known; this form only needs some `k` with `x ^ k = 1`.
-/

@[expose] public section

/-- `a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i` for integer exponents. -/
theorem zpow_sum_eq_prod {ι G : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/-- If `x ^ k = 1` then integer exponents congruent modulo `k` give the same power of `x`. -/
theorem zpow_eq_zpow_of_pow_eq_one {G : Type*} [Group G] {x : G} {k : ℕ} (hx : x ^ k = 1)
    {m n : ℤ} (h : (k : ℤ) ∣ m - n) : x ^ m = x ^ n := by
  obtain ⟨t, ht⟩ := h
  have hxk : x ^ (k : ℤ) = 1 := by rw [zpow_natCast, hx]
  rw [show m = n + k * t by omega, zpow_add, zpow_mul, hxk, one_zpow, mul_one]
