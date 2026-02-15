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
import Mathlib.Data.Nat.Init

namespace Nat
variable {a b c : ℕ}

@[simp] protected lemma dvd_add_mul_self : a ∣ b + c * a ↔ a ∣ b := by
  rw [Nat.dvd_add_left (Nat.dvd_mul_left _ _)]

@[simp] protected lemma dvd_add_self_mul : a ∣ b + a * c ↔ a ∣ b := by
  rw [Nat.mul_comm, Nat.dvd_add_mul_self]

@[simp] protected lemma dvd_mul_self_add : a ∣ b * a + c ↔ a ∣ c := by
  rw [Nat.add_comm, Nat.dvd_add_mul_self]

@[simp] protected lemma dvd_self_mul_add : a ∣ a * b + c ↔ a ∣ c := by
  rw [Nat.mul_comm, Nat.dvd_mul_self_add]

@[simp] lemma dvd_sub_iff_right' (hab : a ∣ b) : a ∣ b - c ↔ a ∣ c ∨ b ≤ c := by
  obtain hbc | hcb := b.le_total c
  · simp [*]
  · simp +contextual [Nat.dvd_sub_iff_right, Nat.le_antisymm hcb, *]

@[simp] lemma dvd_sub_iff_left' (hac : a ∣ c) : a ∣ b - c ↔ a ∣ b ∨ b ≤ c := by
  obtain hbc | hcb := b.le_total c
  · simp [*]
  · simp +contextual [Nat.dvd_sub_iff_left, ← Nat.le_antisymm hcb, *]

@[simp] protected lemma dvd_sub_mul_self : a ∣ b - c * a ↔ a ∣ b ∨ b ≤ c * a := by
  rw [Nat.dvd_sub_iff_left' (Nat.dvd_mul_left _ _)]

@[simp] protected lemma dvd_sub_self_mul : a ∣ b - a * c ↔ a ∣ b ∨ b ≤ c * a := by
  rw [Nat.mul_comm, Nat.dvd_sub_mul_self]

@[simp] protected lemma dvd_mul_self_sub : a ∣ b * a - c ↔ a ∣ c ∨ b * a ≤ c := by
  rw [Nat.dvd_sub_iff_right' (Nat.dvd_mul_left _ _)]

@[simp] protected lemma dvd_self_mul_sub : a ∣ a * b - c ↔ a ∣ c ∨ b * a ≤ c := by
  rw [Nat.mul_comm, Nat.dvd_mul_self_sub]

end Nat
