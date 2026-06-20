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

import Mathlib

/-!
# Mathoverflow 75792

Various questions about integer complexity, which is the minimum number of `1`s needed to express a natural number using addition, multiplication, and parentheses.

Let `‖n‖` denote the integer complexity of `n > 0`.
* It is known that `‖3^n‖ = 3n` for `n > 0`.
* Is it true that `‖2^n‖ = 2n` for `n > 0`?
* The corresponding conjecture for `5` is false, because
  `5^6 = 15625 = 1 + 2^3 * 3^2 * (1 + 2^3 * 3^3)`!

We have chosen to formalise this using an inductive type.

*References:*
 - [mathoverflow/75792](https://mathoverflow.net/a/75792) by user [Harry Altman](https://mathoverflow.net/users/5583)
 - http://arxiv.org/abs/1203.6462 by Jānis Iraids, Kaspars Balodis, Juris Čerņenoks, Mārtiņš Opmanis, Rihards Opmanis, Kārlis Podnieks
 - http://arxiv.org/abs/1207.4841 by Harry Altman, Joshua Zelinsky
 - https://oeis.org/A5245 : Mahler-Popken complexity.
-/

namespace Mathoverflow75792

/-- The inductively defined predicate that `m` is reachable in `n` steps. -/
inductive Reachable : ℕ → ℕ → Prop
  | one : Reachable 1 1
  | add {m n a b} : Reachable m a → Reachable n b → Reachable (m + n) (a + b)
  | mul {m n a b} : Reachable m a → Reachable n b → Reachable (m * n) (a + b)

theorem Reachable.self (n : ℕ) (hn : 0 < n) : Reachable n n :=
  Nat.le_induction .one (fun _ _ ih ↦ .add ih .one) n hn

theorem not_reachable_zero_fst (n : ℕ) : ¬ Reachable 0 n := by
  intro h; generalize hm : 0 = m at h; induction h with
  | one => exact absurd hm (by decide)
  | add h₁ h₂ => rw [eq_comm, add_eq_zero] at hm; aesop
  | mul h₁ h₂ => rw [eq_comm, mul_eq_zero] at hm; aesop

theorem not_reachable_zero_snd (m : ℕ) : ¬ Reachable m 0 := by
  intro h; generalize hn : 0 = n at h; induction h with
  | one => exact absurd hn (by decide)
  | add h₁ h₂ => rw [eq_comm, add_eq_zero] at hn; aesop
  | mul h₁ h₂ => rw [eq_comm, add_eq_zero] at hn; aesop

theorem Reachable.dec {m n : ℕ} (h : Reachable m n) :
    ∃ m' n', m' + 1 = m ∧ n' + 1 = n := by
  obtain _ | m := m
  · exact absurd h (not_reachable_zero_fst _)
  obtain _ | n := n
  · exact absurd h (not_reachable_zero_snd _)
  exact ⟨_, _, rfl, rfl⟩

theorem Reachable.le {m n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (hm : Reachable m n₁) : Reachable m n₂ := by
  induction hn with
  | refl => exact hm
  | step h ih => convert ih.mul .one; simp

theorem reachable_iff_of_two_le (m n : ℕ) (hm : 2 ≤ m) :
    Reachable m n ↔ ∃ m₁, ∃ _ : m₁ < m, ∃ m₂, ∃ _ : m₂ < m, ∃ n₁, ∃ _ : n₁ < n, ∃ n₂, ∃ _ : n₂ < n,
      n₁ + n₂ = n ∧ Reachable m₁ n₁ ∧ Reachable m₂ n₂ ∧ (m₁ + m₂ = m ∨ m₁ * m₂ = m) := by
  refine ⟨fun hmn ↦ ?_, fun ⟨m₁, hm₁, m₂, hm₂, n₁, hn₁, n₂, hn₂, h₁, h₂, h₃, h₄⟩ ↦
    h₁ ▸ h₄.casesOn (· ▸ .add h₂ h₃) (· ▸ .mul h₂ h₃)⟩
  induction hmn with
  | one => exact absurd hm (by decide)
  | @add m₃ m₄ n₃ n₄ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨m₃, n₃, rfl, rfl⟩ := h₁.dec
      obtain ⟨m₄, n₄, rfl, rfl⟩ := h₂.dec
      refine ⟨m₃ + 1, ?_, m₄ + 1, ?_, n₃ + 1, ?_, n₄ + 1, ?_, rfl, h₁, h₂, .inl rfl⟩ <;> omega
  | @mul m₃ m₄ n₃ n₄ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨m₃, n₃, rfl, rfl⟩ := h₁.dec
      obtain ⟨m₄, n₄, rfl, rfl⟩ := h₂.dec
      obtain _ | m₃ := m₃
      · obtain ⟨m₅, hm₅, m₆, hm₆, n₅, hn₅, n₆, hn₆, h₃, h₄, h₅, h₆⟩ := ih₂ (by omega)
        refine ⟨m₅, ?_, m₆, ?_, n₅+n₃+1, ?_, n₆, ?_, by rw [← h₃]; ring, h₄.le ?_, h₅, ?_⟩
        all_goals omega
      obtain _ | m₄ := m₄
      · obtain ⟨m₅, hm₅, m₆, hm₆, n₅, hn₅, n₆, hn₆, h₃, h₄, h₅, h₆⟩ := ih₁ (by omega)
        refine ⟨m₅, ?_, m₆, ?_, n₅, ?_, n₆+n₄+1, ?_, by rw [← h₃]; ring, h₄, h₅.le ?_, ?_⟩
        all_goals omega
      refine ⟨m₃+2, ?_, m₄+2, ?_, _, ?_, _, ?_, rfl, h₁, h₂, .inr rfl⟩
      · refine (Nat.lt_mul_iff_one_lt_right ?_).2 ?_ <;> omega
      · refine (Nat.lt_mul_iff_one_lt_left ?_).2 ?_ <;> omega
      all_goals omega

instance Reachable.decide : ∀ m n, Decidable (Reachable m n)
  | 0, n => isFalse (not_reachable_zero_fst n)
  | 1, 0 => isFalse (not_reachable_zero_snd 1)
  | 1, n+1 => isTrue (Reachable.one.le (by omega))
  | m+2, n => by
      let d : ∀ {m₁} (h : m₁ < m + 2) {n}, Decidable (Reachable m₁ n) :=
        fun h ↦ Reachable.decide _ _
      refine @decidable_of_iff' _ _ (reachable_iff_of_two_le (m+2) n (by omega)) ?_
      refine Nat.decidableExistsLT' (I := fun m₁ hm₁ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun m₂ hm₂ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun n₁ hn₁ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun n₂ hn₂ ↦ ?_)
      refine instDecidableAnd (dq := ?_)
      refine instDecidableAnd (dp := d hm₁) (dq := ?_)
      exact instDecidableAnd (dp := d hm₂)

/--
The [(Mahler-Popken) complexity of `n`](https://en.wikipedia.org/wiki/Integer_complexity):
the minimum number of `1`s needed to express a given number using only addition and
multiplication. E.g. `2 = 1 + 1`, so `complexity 2 = 2`.
-/
def complexity (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else Nat.find ⟨n, Reachable.self n <| n.pos_of_ne_zero h⟩

theorem Reachable.complexity_le {m n : ℕ} (h : Reachable m n) : complexity m ≤ n := by
  unfold complexity
  split_ifs with h'
  · subst h'; exact absurd h (not_reachable_zero_fst n)
  exact Nat.find_min' _ h

theorem Reachable.complexity_eq {m n : ℕ} (h : Reachable m n)
    (min : ∀ n' < n, ¬ Reachable m n') : complexity m = n := by
  refine le_antisymm h.complexity_le ?_
  unfold complexity
  split_ifs with h'
  · subst h'; exact absurd h (not_reachable_zero_fst n)
  exact (Nat.le_find_iff _ _).2 min

theorem Reachable.complexity {n : ℕ} (hn : 0 < n) : Reachable n (complexity n) := by
  unfold Mathoverflow75792.complexity
  rw [dif_neg (ne_of_gt hn)]
  exact Nat.find_spec _

theorem complexity_zero : complexity 0 = 0 := rfl

theorem complexity_one : complexity 1 = 1 :=
  Reachable.one.complexity_eq fun n' hn' ↦ by
    have : n' = 0 := by omega
    subst this; exact not_reachable_zero_snd 1

theorem complexity_two : complexity 2 = 2 :=
  (Reachable.add .one .one).complexity_eq fun n' hn' ↦ by
    interval_cases n'
    · exact not_reachable_zero_snd 2
    · rw [reachable_iff_of_two_le 2 1 (by omega)]
      rintro ⟨m₁, hm₁, m₂, hm₂, n₁, hn₁, n₂, hn₂, h₁, -⟩
      omega

theorem Reachable.pow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : Reachable (m ^ n) (m * n) := by
  induction hn with
  | refl => convert Reachable.self m hm <;> simp
  | step hn ih => exact .mul ih (.self m hm)

theorem Reachable.pow' (m n : ℕ+) : Reachable (m ^ (n : ℕ) : ℕ) (m * n) :=
  .pow _ _ m.pos n.pos

/-- `5^6 = 15625 = 1 + 2^3 * 3^2 * (1 + 2^3 * 3^3)`! -/
theorem Reachable.five_pow_six : Reachable (5^6) 29 :=
  have h8 : Reachable 8 6 := .pow' 2 3
  have h9 : Reachable 9 6 := .pow' 3 2
  have h27 : Reachable 27 9 := .pow' 3 3
  .add .one <| .mul h8 <| .mul h9 <| .add .one <| .mul h8 h27

/-- Is `5n` the complexity of `5^n` for `0 < n`? Answer: No. -/
theorem complexity_five_pow : False ↔ ∀ n : ℕ, 0 < n → complexity (5 ^ n) = 5 * n := by
  show False ↔ _
  simp [false_iff, not_forall]
  exact ⟨6, by decide, fun h ↦ absurd (h ▸ Reachable.five_pow_six.complexity_le) (by decide)⟩

/-- Is `3n` the complexity of `3^n` for `0 < n`? Answer: Yes, by John Selfridge.

Reference: https://arxiv.org/abs/1207.4841
-/
theorem complexity_three_pow : True ↔ ∀ n : ℕ, 0 < n → complexity (3 ^ n) = 3 * n := by
  sorry

/-- Is `2n` the complexity of `2^n` for `0 < n`? -/
theorem complexity_two_pow : True ↔ ∀ n : ℕ, 0 < n → complexity (2 ^ n) = 2 * n := by
  sorry

end Mathoverflow75792
