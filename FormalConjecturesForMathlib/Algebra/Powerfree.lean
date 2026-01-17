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

import Mathlib.Algebra.Squarefree.Basic

variable {M M₀ : Type*}

def Powerfree [Monoid M] (m : M) (k : ℕ) : Prop :=
  ∀ ⦃x : M⦄, x ^ k ∣ m → IsUnit x

section Monoid

theorem powerfree_monotone [Monoid M] {m : M} {a b : ℕ} (hab : a ≤ b) (hm : Powerfree m a) :
  Powerfree m b := fun x hx => hm (dvd_of_mul_right_dvd (pow_mul_pow_sub x hab ▸ hx))

theorem powerfree_antitone [Monoid M] {r m : M} {k : ℕ} (hrm : r ∣ m) (hm : Powerfree m k) :
    Powerfree r k := fun _ hx => hm (hx.trans hrm)

@[simp]
theorem powerfree_two [Monoid M] {m : M} : Powerfree m 2 ↔ Squarefree m where
  mp h x hx := h (sq x ▸ hx)
  mpr h x hx := h x (sq x ▸ hx)

theorem IsUnit.powerfree [CommMonoid M] {m : M} (h : IsUnit m) {k : ℕ} (hk : k ≠ 0) :
    Powerfree m k := fun _ hx => (isUnit_pow_iff hk).1 (isUnit_of_dvd_unit hx h)

@[simp]
theorem powerfree_one [CommMonoid M] {k : ℕ} (hk : k ≠ 0) : Powerfree (1 : M) k :=
  isUnit_one.powerfree hk

theorem Irreducible.powerfree [CommMonoid M] {m : M} (h : Irreducible m) {k : ℕ} (hk : 2 ≤ k) :
    Powerfree m k := by
  rintro y ⟨z, hz⟩
  induction k with
  | zero => grind
  | succ n ih =>
  rw [← npow_eq_pow, Monoid.npow_succ, mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact (isUnit_pow_iff (by linarith)).1 hu
  · apply isUnit_of_mul_isUnit_left hu

end Monoid

section MonoidWithZero

@[simp]
theorem not_powerfree_zero [MonoidWithZero M₀] [Nontrivial M₀] (k : ℕ) :
    ¬ Powerfree (0 : M₀) k := by
  rw [Powerfree, not_forall]
  exact ⟨0, by simp⟩

theorem Prime.powerfree [CancelCommMonoidWithZero M₀] {x : M₀} (h : Prime x) {k : ℕ} (hk : 2 ≤ k) :
    Powerfree x k := h.irreducible.powerfree hk

end MonoidWithZero
