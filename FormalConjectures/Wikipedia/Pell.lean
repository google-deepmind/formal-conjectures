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

/-!
# Infinitude of Pell number primes

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Pell_number#Primes_and_squares)
 - [A86383](https://oeis.org/A86383)

The Pell numbers $P_n$ are defined by $P_0 = 0$,
$P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$. [OEIS A129](https://oeis.org/A129)

The conjecture says that there are infinitely many prime Pell numbers.
-/

namespace PellNumbers

/-- The *Pell numbers* $P_n$ are defined by $P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$ -/
def pellNumber : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 + 1 => 2 * pellNumber (n + 1) + pellNumber n

@[category test, AMS 11]
theorem pellNumber_zero : pellNumber 0 = 0 := rfl

@[category test, AMS 11]
theorem pellNumber_one : pellNumber 1 = 1 := rfl

@[category test, AMS 11]
theorem pellNumber_two : pellNumber 2 = 2 := rfl

@[category test, AMS 11]
theorem pellNumber_five : pellNumber 5 = 29 := rfl

/-- Similar to Fibonacci numbers, there exist numerous identites around Pell numbers, i.e.
P_{2n+1} = P_n ^ 2 + P_{n+1} ^ 2 -/
@[category textbook, AMS 11]
theorem pellNumber_sq_add_pellNumber_succ_sq (n : ℕ) :
    pellNumber (2 * n + 1) = pellNumber n ^ 2 + pellNumber (n + 1) ^ 2 := by
  -- Prove jointly with the even-index companion
  --   P(2n+2) = 2 · P(n+1) · (P(n) + P(n+1)),
  -- since each successive case needs both formulas at the previous index.
  suffices h : ∀ n,
      pellNumber (2 * n + 1) = pellNumber n ^ 2 + pellNumber (n + 1) ^ 2 ∧
      pellNumber (2 * n + 2) =
        2 * pellNumber (n + 1) * (pellNumber n + pellNumber (n + 1)) by
    exact (h n).1
  intro n
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> rfl
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    -- The Pell recursion at the next pair of indices.
    have hstep1 : pellNumber (2 * (k + 1) + 1) =
        2 * pellNumber (2 * k + 2) + pellNumber (2 * k + 1) := by
      show pellNumber (2 * k + 1 + 1 + 1) =
        2 * pellNumber (2 * k + 1 + 1) + pellNumber (2 * k + 1)
      rfl
    have hstep2 : pellNumber (2 * (k + 1) + 2) =
        2 * pellNumber (2 * (k + 1) + 1) + pellNumber (2 * k + 2) := by
      show pellNumber (2 * k + 2 + 1 + 1) =
        2 * pellNumber (2 * k + 2 + 1) + pellNumber (2 * k + 2)
      rfl
    have hk2 : pellNumber (k + 2) = 2 * pellNumber (k + 1) + pellNumber k := rfl
    -- A(k+1): prove once, use as first conjunct and inside the B(k+1) step.
    have hA' : pellNumber (2 * (k + 1) + 1) =
        pellNumber (k + 1) ^ 2 + pellNumber (k + 2) ^ 2 := by
      rw [hstep1, hA, hB, hk2]; ring
    refine ⟨hA', ?_⟩
    rw [hstep2, hA', hB, hk2]; ring

/-- An explicit formula for Pell numbers, similar to Binet's formula -/
@[category textbook, AMS 11]
theorem coe_pellNumber_eq : ∀ n, (pellNumber n : ℝ) = ((1 + √2) ^ n - (1 - √2) ^ n) / (2 * √2) := by
  sorry

/-- There are infinitely many prime Pell numbers -/
@[category research open, AMS 11]
theorem infinite_pellNumber_primes : Infinite {n : ℕ | Prime (pellNumber n)} := by
  sorry

-- TODO : Formalise connection between Pell numbers and Pell equation x^2 - 2*y^2 = -1

end PellNumbers
