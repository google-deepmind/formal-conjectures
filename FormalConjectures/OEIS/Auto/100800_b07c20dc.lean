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

import FormalConjectures.Util.ProblemImports
open Nat Function Classical

/-- The sum of the decimal digits of a natural number. -/
def sum_digits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum

/-- The function $f(n) = n + \text{sum of the digits of } n$. -/
def f (n : ℕ) : ℕ := n + sum_digits n

/--
A100800: Let $f(n) = n + \text{sum of the digits of } n$. If $f(n)$ is multiple of $n$ then $a(n)= f(n)$ else $a(n) = f(f(f(n)))\dots$ until one gets a multiple of $n$; $a(n) = 0$ if no such number exists.
-/
noncomputable def A100800 (n : ℕ) : ℕ :=
  -- P(k) holds if the (k+1)-th iteration of f is a multiple of n.
  -- k=0 corresponds to the first iteration, f(n).
  let P (k : ℕ) : Prop := n ∣ Nat.iterate f (k + 1) n

  -- We use the noncomputable definition of finding the minimum index if it exists,
  -- or returning 0 otherwise, using the standard classical definition pattern.
  dite (∃ k, P k)
    (fun h_exists =>
      let k₀ : ℕ := Nat.find h_exists
      Nat.iterate f (k₀ + 1) n)
    (fun _ => 0)


theorem a_one : A100800 1 = 2 := by
  delta A100800
  norm_num[f,bot_unique ∘Nat.find_min' _,id]
  norm_num[sum_digits]

theorem a_two : A100800 2 = 4 := by
  rw [←eq_comm, A100800]
  delta f
  norm_num[sum_digits,Exists.intro 1,Nat.find_eq_iff]
  rw[Nat.find_eq_iff _|>.2,Function.iterate_zero_apply]
  decide

theorem a_three : A100800 3 = 6 := by
  norm_num[A100800]
  delta f
  norm_num[sum_digits,Exists.intro 0,Function.comp,Nat.find_eq_iff]
  exact (congr_arg₂ _ ↑(bot_unique ↑(Nat.find_min' _ (by(norm_num)))) rfl )

theorem a_four : A100800 4 = 8 := by
  (inhabit ℝ)
  norm_num[A100800]
  delta f
  norm_num[sum_digits,Exists.intro 0]
  exact (congr_arg₂ _ (bot_unique (Nat.find_min' _ (by norm_num[Function.iterate_succ_apply _ _]))) rfl )

/-- A100800 Conjecture: No term is zero. -/
theorem oeis_100800_conjecture_0 : ∀ (n : ℕ), n ≠ 0 → A100800 n ≠ 0 := by
  sorry
