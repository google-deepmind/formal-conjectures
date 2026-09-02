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

open Nat Finset

/--
A308934: Number of ways to write $n$ as $(2^a 3^b)^2 + (2^c 3^d)^2 + x^2 + 2 y^2$,
where $a, b, c, d, x, y$ are nonnegative integers with $2^a 3^b \ge 2^c 3^d$.
-/
def A308934 (n : ℕ) : ℕ :=
  -- Note: Nat.log b n in Lean is $\lfloor \log_b n \rfloor$.
  -- Since $2^{2a} \le n$, $a \le \lfloor \log_2 n / 2 \rfloor$.
  let max_e2 := (Nat.log 2 n / 2) + 1
  let max_e3 := (Nat.log 3 n / 2) + 1

  -- Maximum value for y: $2y^2 \le n \implies y \le \sqrt{n/2}$.
  let max_y := Nat.sqrt (n / 2)

  -- Helper function for the base of the squares $2^k 3^l$.
  let r (k l : ℕ) : ℕ := (2^k * 3^l)

  -- The condition for $m$ to be a square is that its integer square root squared equals $m$.
  let is_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m

  -- The overall count is a sum over all valid exponents a, b, c, d.
  Finset.sum (range max_e2) fun a =>
    Finset.sum (range max_e3) fun b =>
      let r_val := r a b

      Finset.sum (range max_e2) fun c =>
        Finset.sum (range max_e3) fun d =>
          let s_val := r c d

          -- Enforce the condition $2^a 3^b \geq 2^c 3^d$.
          if r_val < s_val then 0 else

          -- Pruning: if $r^2 + s^2 > n$.
          if r_val^2 + s_val^2 > n then 0 else

          -- Count the number of valid $y$'s.
          Finset.card $ Finset.filter (fun y =>
            let k := r_val^2 + s_val^2 + 2 * y^2

            -- Check $r^2 + s^2 + 2y^2 \le n$, and the remainder $n - k$ is a square $x^2$.
            k ≤ n ∧ is_square (n - k)
          ) (range (max_y + 1))


theorem a_one : A308934 1 = 0 := by
  sorry

theorem a_two : A308934 2 = 1 := by
  sorry

theorem a_three : A308934 3 = 1 := by
  sorry

theorem a_four : A308934 4 = 1 := by
  sorry


/-- A308934 Conjecture 1: a(n) > 0 for all n > 1. -/
theorem oeis_308934_conjecture_0 (n : ℕ) (hn : n > 1) : A308934 n > 0 := by
  sorry
