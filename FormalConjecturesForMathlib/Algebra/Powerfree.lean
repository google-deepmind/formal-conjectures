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

variable {R : Type*}

def Powerfree [Monoid R] (r : R) (k : ℕ) : Prop :=
  ∀ x : R, x ^ k ∣ r → IsUnit x

theorem powerfree_iff_squarefree [Monoid R] (r : R) : Powerfree r 2 ↔ Squarefree r where
  mp h x hx := h x (sq x ▸ hx)
  mpr h x hx := h x ((sq x).symm ▸ hx)

theorem IsUnit.powerfree [CommMonoid R] {r : R} (h : IsUnit r) {k : ℕ} (hk : k ≠ 0) :
    Powerfree r k := fun _ hx => (isUnit_pow_iff hk).1 (isUnit_of_dvd_unit hx h)

theorem powerfree_one [CommMonoid R] {k : ℕ} (hk : k ≠ 0) : Powerfree (1 : R) k :=
  isUnit_one.powerfree hk

theorem not_powerfree_zero [MonoidWithZero R] [Nontrivial R] (k : ℕ) : ¬ Powerfree (0 : R) k := by
  rw [Powerfree, not_forall]
  exact ⟨0, by simp⟩

theorem Irreducible.powerfree [CommMonoid R] {r : R} (h : Irreducible r) {k : ℕ} (hk : k ≥ 2) :
    Powerfree r k := by
  rintro y ⟨z, hz⟩
  induction k with
  | zero => grind
  | succ n ih =>
  rw [← npow_eq_pow, Monoid.npow_succ, mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact (isUnit_pow_iff (by linarith)).1 hu
  · apply isUnit_of_mul_isUnit_left hu

theorem Prime.powerfree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) {k : ℕ} (hk : k ≥ 2) :
    Powerfree x k := h.irreducible.powerfree hk
