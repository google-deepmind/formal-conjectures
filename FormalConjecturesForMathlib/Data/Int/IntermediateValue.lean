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

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Init

/-!
# A discrete intermediate value theorem

An integer-valued sequence whose consecutive terms differ by at most `1` attains every
integer value lying between two of its terms. This is the discrete analogue of the
intermediate value theorem for a unit-step walk on `ℤ`.
-/

@[expose] public section

/-- **Discrete intermediate value theorem.** If an integer-valued sequence `f : ℕ → ℤ` has
consecutive terms differing by at most `1`, then it attains every value between `f a` and
`f b`: for `a ≤ b` and `f a ≤ t ≤ f b` there is some index `c ∈ [a, b]` with `f c = t`. -/
theorem Int.exists_eq_of_natAbs_sub_le_one (f : ℕ → ℤ)
    (hf : ∀ n, (f (n + 1) - f n).natAbs ≤ 1) {a b : ℕ} (hab : a ≤ b) {t : ℤ}
    (hta : f a ≤ t) (htb : t ≤ f b) : ∃ c, a ≤ c ∧ c ≤ b ∧ f c = t := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, le_refl a, le_refl a, le_antisymm hta htb⟩
  | succ b hb ih =>
    by_cases h : t ≤ f b
    · obtain ⟨c, hac, hcb, hfc⟩ := ih h
      exact ⟨c, hac, by omega, hfc⟩
    · have hstep := hf b
      exact ⟨b + 1, by omega, le_refl _, by omega⟩
