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

public import FormalConjecturesUtil

/-!
# Unique Crystal Components

*Reference:* [arxiv/1601.03081](https://arxiv.org/abs/1601.03081)
**The Biharmonic mean**
by *Marco Abrate, Stefano Barbero, Umberto Cerruti, Nadir Murru*
-/

@[expose] public section

namespace Arxiv.«1601.03081»

/--
An odd number $n$ is called a crystal if $n = ab$, with $a, b > 1$
and $B(a, b) ∈ ℕ$, where $B(a, b) := ((a + b)^2 + (a b + 1)^2) / (2 (a + 1) (b + 1))$.
-/
def IsCrystalWithComponents (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2

@[category test, AMS 11]
theorem isCrystalWithComponents_35_5_7 : IsCrystalWithComponents 35 5 7 := by
  norm_num [IsCrystalWithComponents]

/-- The $B \iff P$ divisibility equivalence from Proposition 1. Oddness of $a$ suffices. -/
@[category API, AMS 11]
theorem biharmonic_dvd_iff_product (a b : ℕ) (ha : Odd a) :
    2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2 ↔
      (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) := by
  obtain ⟨k, hk⟩ := ha
  have hden : 2 * (a + 1) * (b + 1) ∣ ((a + 1) * (b + 1))^2 := by
    refine ⟨(k + 1) * (b + 1), ?_⟩
    rw [hk]
    ring
  have hid : (a + b)^2 + (a * b + 1)^2 + 2 * ((a + b) * (a * b + 1)) =
      ((a + 1) * (b + 1))^2 := by ring
  have hd : 2 * (a + 1) * (b + 1) ∣
      (a + b)^2 + (a * b + 1)^2 + 2 * ((a + b) * (a * b + 1)) := hid ▸ hden
  calc
    _ ↔ 2 * (a + 1) * (b + 1) ∣ 2 * ((a + b) * (a * b + 1)) :=
      ⟨fun h => (Nat.dvd_add_iff_right h).mpr hd,
        fun h => (Nat.dvd_add_iff_left h).mpr hd⟩
    _ ↔ _ := by rw [Nat.mul_assoc, Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]

/-- The $P \iff Q$ divisibility equivalence from Proposition 1. -/
@[category API, AMS 11]
theorem product_dvd_iff_sum_sq (a b : ℕ) :
    (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) ↔
      (a + 1) * (b + 1) ∣ (a + b)^2 := by
  have hd : (a + 1) * (b + 1) ∣ (a + b)^2 + (a + b) * (a * b + 1) := by
    have hid : (a + b)^2 + (a + b) * (a * b + 1) =
        (a + b) * ((a + 1) * (b + 1)) := by ring
    rw [hid]
    exact dvd_mul_left _ _
  exact ⟨fun h => (Nat.dvd_add_iff_left h).mpr hd,
    fun h => (Nat.dvd_add_iff_right h).mpr hd⟩

/-- The $P \iff F$ divisibility equivalence from Proposition 1. -/
@[category API, AMS 11]
theorem product_dvd_iff_mul_sq (a b : ℕ) :
    (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) ↔
      (a + 1) * (b + 1) ∣ (a * b + 1)^2 := by
  have hd : (a + 1) * (b + 1) ∣ (a * b + 1)^2 + (a + b) * (a * b + 1) := by
    have hid : (a * b + 1)^2 + (a + b) * (a * b + 1) =
        (a * b + 1) * ((a + 1) * (b + 1)) := by ring
    rw [hid]
    exact dvd_mul_left _ _
  exact ⟨fun h => (Nat.dvd_add_iff_left h).mpr hd,
    fun h => (Nat.dvd_add_iff_right h).mpr hd⟩

/-- Crystal components satisfy the equivalent $P$ divisibility condition of Proposition 1. -/
@[category API, AMS 11]
theorem isCrystalWithComponents_iff_product_dvd (n a b : ℕ) :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧
        (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) := by
  unfold IsCrystalWithComponents
  refine and_congr_right fun hn => and_congr_right fun _ => and_congr_right fun _ => ?_
  refine and_congr_right fun hab => ?_
  exact biharmonic_dvd_iff_product a b (Nat.Odd.of_mul_left (hab ▸ hn))

/-- Crystal components satisfy the equivalent $Q$ divisibility condition of Proposition 1. -/
@[category API, AMS 11]
theorem isCrystalWithComponents_iff_sum_sq_dvd (n a b : ℕ) :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ (a + 1) * (b + 1) ∣ (a + b)^2 := by
  rw [isCrystalWithComponents_iff_product_dvd, product_dvd_iff_sum_sq]

/-- Crystal components satisfy the equivalent $F$ divisibility condition of Proposition 1. -/
@[category API, AMS 11]
theorem isCrystalWithComponents_iff_mul_sq_dvd (n a b : ℕ) :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ (a + 1) * (b + 1) ∣ (a * b + 1)^2 := by
  rw [isCrystalWithComponents_iff_product_dvd, product_dvd_iff_mul_sq]

-- TODO(firsching): formalize the recurrent-sequence characterization from section 3.

/--
If $n = ab$ is a crystal, then there are no other pairs of
positive integers $c, d > 1$, different from the couple $a, b$, such that $n = cd$ and
$B(c, d) ∈ ℕ$, i.e., the components of the crystals are unique.
-/
@[category research open, AMS 11 26]
theorem crystals_components_unique (n a b c d : ℕ)
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d) :
    ({a, b} : Finset ℕ) = {c, d} := by
  sorry

end Arxiv.«1601.03081»
