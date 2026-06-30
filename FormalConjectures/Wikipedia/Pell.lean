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
  -- The characteristic polynomial of the Pell recursion is $x^2 = 2x + 1$, with
  -- roots $\alpha = 1 + \sqrt{2}$ and $\beta = 1 - \sqrt{2}$. The function
  -- $f(n) = (\alpha^n - \beta^n) / (2\sqrt{2})$ satisfies the same recursion
  -- and the same base cases, so it agrees with the cast of `pellNumber`.
  set α : ℝ := 1 + √2 with hα_def
  set β : ℝ := 1 - √2 with hβ_def
  -- Basic facts about α and β.
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hα_sq : α ^ 2 = 2 * α + 1 := by rw [hα_def]; ring_nf; linarith [hsq2]
  have hβ_sq : β ^ 2 = 2 * β + 1 := by rw [hβ_def]; ring_nf; linarith [hsq2]
  have h2sq2_ne : (2 * √2 : ℝ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  -- The characteristic-poly identity lifts to $x^{n+2} = 2 x^{n+1} + x^n$.
  have hα_rec : ∀ n, α ^ (n + 2) = 2 * α ^ (n + 1) + α ^ n := by
    intro n
    have : α ^ (n + 2) = α ^ n * α ^ 2 := by ring
    rw [this, hα_sq]; ring
  have hβ_rec : ∀ n, β ^ (n + 2) = 2 * β ^ (n + 1) + β ^ n := by
    intro n
    have : β ^ (n + 2) = β ^ n * β ^ 2 := by ring
    rw [this, hβ_sq]; ring
  -- Joint induction on consecutive indices.
  suffices h : ∀ n,
      (pellNumber n : ℝ) = (α ^ n - β ^ n) / (2 * √2) ∧
      (pellNumber (n + 1) : ℝ) = (α ^ (n + 1) - β ^ (n + 1)) / (2 * √2) from
    fun n => (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [pellNumber]
    · -- pellNumber 1 = 1 and (α - β) / (2√2) = (2√2) / (2√2) = 1.
      simp only [pellNumber, pow_one, Nat.cast_one, zero_add]
      rw [hα_def, hβ_def]
      field_simp; ring
  | succ k ih =>
    obtain ⟨hk, hk1⟩ := ih
    refine ⟨hk1, ?_⟩
    -- pellNumber (k+2) = 2 * pellNumber (k+1) + pellNumber k, both sides cast to ℝ.
    have hrec : pellNumber (k + 1 + 1) = 2 * pellNumber (k + 1) + pellNumber k := rfl
    show (pellNumber (k + 1 + 1) : ℝ) = (α ^ (k + 1 + 1) - β ^ (k + 1 + 1)) / (2 * √2)
    rw [hrec]
    push_cast
    rw [hk1, hk, hα_rec k, hβ_rec k]
    field_simp
    ring

/-- There are infinitely many prime Pell numbers -/
@[category research open, AMS 11]
theorem infinite_pellNumber_primes : Infinite {n : ℕ | Prime (pellNumber n)} := by
  sorry

-- TODO : Formalise connection between Pell numbers and Pell equation x^2 - 2*y^2 = -1

end PellNumbers
