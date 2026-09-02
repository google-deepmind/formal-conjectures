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

open Nat BigOperators

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$,
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  -- Helper for the binomial coefficient term: B(k) = binomial(2*k+1, k)
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k

  -- The maximum value for $a, b$ is $\lfloor \sqrt{n} \rfloor$.
  -- We use a safe upper bound for iteration. `n.sqrt + 1` is slightly more than needed, but safe.
  let R_sq := Finset.range (n.sqrt + 1)
  -- The maximum value for $c, d$ is when B(c) is not too large. Since B(0)=1, B(1)=3, B(2)=10,
  -- a rough upper bound for k is needed, n+1 is certainly safe but inefficient.
  -- A tighter bound is not strictly necessary for definition.
  -- Since $\binom{2k+1}{k} \approx 4^k / \sqrt{\pi k}$, we only need to iterate c and d up to around log_4(n).
  -- For formalization, we keep the provided `n+1` range or a slightly better one.
  let R_binom := Finset.range (n + 1)

  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

theorem a_one : a 1 = 0 := by
  sorry

theorem a_two : a 2 = 1 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

theorem a_four : a 4 = 2 := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 1.
-/
theorem oeis_303639_conjecture_0 : ∀ (n : ℕ), n > 1 → a n > 0 := by
  sorry
