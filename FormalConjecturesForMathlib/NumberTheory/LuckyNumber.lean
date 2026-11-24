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

public import Mathlib.Data.Nat.Notation

/-!
# Ulam's lucky numbers

This file defines the positional sieve `luckySieve`, the $n$-th lucky number `luckyNumber`, the
membership predicate `IsLuckyNumber` (OEIS A000959), and proves sieve stabilization.
-/

@[expose] public section

/-- Positional sieve generating Ulam's lucky sequence: `luckySieve 0 i = 2i + 1`, and stage `s + 1`
deletes every $m$-th surviving position where $m = \text{luckySieve } s\ (s + 1)$. -/
def luckySieve : ℕ → ℕ → ℕ
  | 0, i => 2 * i + 1
  | s + 1, i =>
    let m := luckySieve s (s + 1)
    luckySieve s (i + i / (m - 1))

/-- The $n$-th lucky number (0-indexed: $1, 3, 7, 9, 13, 15, 21, 25, 31, \dots$), using
stabilization of `luckySieve s n` once $s \ge n$. -/
def luckyNumber (n : ℕ) : ℕ :=
  luckySieve n n

/-- Membership predicate for Ulam's lucky sequence (OEIS A000959). -/
def IsLuckyNumber (k : ℕ) : Prop :=
  ∃ n : ℕ, luckyNumber n = k

/-- Every entry at every stage of Ulam's lucky sieve is odd. -/
theorem luckySieve_mod_two (s i : ℕ) : luckySieve s i % 2 = 1 := by
  induction s generalizing i with
  | zero => dsimp [luckySieve]; omega
  | succ s ih => exact ih _

/-- Once the sieve stage $s$ reaches at least $n$, `luckySieve s n` stabilizes at
`luckyNumber n`. -/
theorem luckySieve_stabilizes {n s : ℕ} (hns : n ≤ s) :
    luckySieve s n = luckyNumber n := by
  have hge : ∀ t i : ℕ, 2 * i + 1 ≤ luckySieve t i := fun t => by
    induction t with
    | zero => intro i; dsimp [luckySieve]; omega
    | succ t ih =>
      intro i; dsimp [luckySieve]
      have h1 := ih (i + i / (luckySieve t (t + 1) - 1))
      have h2 := Nat.le_add_right i (i / (luckySieve t (t + 1) - 1)); omega
  induction s with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    rfl
  | succ s ih =>
    by_cases hle : n ≤ s
    · dsimp [luckySieve]
      have := hge s (s + 1)
      rw [Nat.div_eq_of_lt (by omega), Nat.add_zero, ih hle]
    · have hn : n = s + 1 := by omega
      subst hn
      rfl
