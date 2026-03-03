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

/-- Recurrence: P(n+2) = 2*P(n+1) + P(n) -/
private lemma pellNumber_rec (n : ℕ) :
    pellNumber (n + 2) = 2 * pellNumber (n + 1) + pellNumber n := rfl

/--
Key helper: prove both
  A(n): P(2n+1) = P(n)^2 + P(n+1)^2
  B(n): P(2n) = 2*P(n)*P(n+1) - 2*P(n)^2
together by induction in ℤ.
-/
private lemma pellNumber_double_ind (n : ℕ) :
    (pellNumber (2 * n + 1) : ℤ) = (pellNumber n) ^ 2 + (pellNumber (n + 1)) ^ 2 ∧
    (pellNumber (2 * n) : ℤ) = 2 * (pellNumber n) * (pellNumber (n + 1)) -
      2 * (pellNumber n) ^ 2 := by
  induction n with
  | zero => constructor <;> simp [pellNumber]
  | succ k ih =>
    obtain ⟨ihA, ihB⟩ := ih
    -- Cast the recurrence at various indices
    have hRec : (pellNumber (k + 2) : ℤ) = 2 * pellNumber (k + 1) + pellNumber k := by
      exact_mod_cast pellNumber_rec k
    -- P(2k+2) = 2*P(2k+1) + P(2k)
    have hP2k2 : (pellNumber (2 * k + 2) : ℤ) = 2 * pellNumber (2 * k + 1) + pellNumber (2 * k) := by
      have : pellNumber (2 * k + 2) = 2 * pellNumber (2 * k + 1) + pellNumber (2 * k) := by
        have h : 2 * k + 2 = (2 * k) + 2 := by ring
        rw [h, pellNumber_rec]
      exact_mod_cast this
    -- P(2k+3) = 2*P(2k+2) + P(2k+1)
    have hP2k3 : (pellNumber (2 * k + 3) : ℤ) = 2 * pellNumber (2 * k + 2) + pellNumber (2 * k + 1) := by
      have : pellNumber (2 * k + 3) = 2 * pellNumber (2 * k + 2) + pellNumber (2 * k + 1) := by
        have h : 2 * k + 3 = (2 * k + 1) + 2 := by ring
        rw [h, pellNumber_rec]
      exact_mod_cast this
    constructor
    · -- Goal: P(2*(k+1)+1) = P(k+1)^2 + P(k+2)^2
      -- 2*(k+1)+1 = 2k+3
      have heq1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      have heq2 : k + 1 + 1 = k + 2 := by omega
      simp only [heq1, heq2]
      rw [hP2k3, hP2k2, ihA, ihB, hRec]
      ring
    · -- Goal: P(2*(k+1)) = 2*P(k+1)*P(k+2) - 2*P(k+1)^2
      -- 2*(k+1) = 2k+2
      have heq1 : 2 * (k + 1) = 2 * k + 2 := by omega
      have heq2 : k + 1 + 1 = k + 2 := by omega
      simp only [heq1, heq2]
      rw [hP2k2, ihA, ihB, hRec]
      ring

/-- Similar to Fibonacci numbers, there exist numerous identites around Pell numbers, i.e.
P_{2n+1} = P_n ^ 2 + P_{n+1} ^ 2 -/
@[category high_school, AMS 11]
theorem pellNumber_sq_add_pellNumber_succ_sq (n : ℕ) :
    pellNumber (2 * n + 1) = pellNumber n ^ 2 + pellNumber (n + 1) ^ 2 := by
  have := (pellNumber_double_ind n).1
  exact_mod_cast this

/-- An explicit formula for Pell numbers, similar to Binet's formula.
Proof: strong induction using the recurrence P(n+2) = 2*P(n+1) + P(n),
verified by showing both sides satisfy the same recurrence with same initial values. -/
@[category high_school, AMS 11]
theorem coe_pellNumber_eq : ∀ n, (pellNumber n : ℝ) = ((1 + √2) ^ n - (1 - √2) ^ n) / (2 * √2) := by
  intro n
  have hsqrt2_pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2sqrt2_ne : (2 : ℝ) * √2 ≠ 0 := by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [pellNumber]
  | 1 =>
    -- (1+√2)^1 - (1-√2)^1 = 2√2, so result = 2√2/(2√2) = 1
    simp only [pellNumber, pow_one, Nat.cast_one]
    have : (1 + √2) - (1 - √2) = 2 * √2 := by ring
    rw [this, div_self h2sqrt2_ne]
  | n + 2 =>
    have ih1 := ih (n + 1) (by omega)
    have ih0 := ih n (by omega)
    push_cast [pellNumber_rec n]
    rw [ih1, ih0]
    -- Key: (1±√2)^(n+2) = 2*(1±√2)^(n+1) + (1±√2)^n
    -- because (1±√2)^2 = 2*(1±√2) + 1
    have hrec_plus : (1 + √2) ^ (n + 2) = 2 * (1 + √2) ^ (n + 1) + (1 + √2) ^ n := by
      have h : (1 + √2) ^ 2 = 2 * (1 + √2) + 1 := by
        ring_nf; nlinarith [hsqrt2_sq]
      calc (1 + √2) ^ (n + 2) = (1 + √2) ^ n * (1 + √2) ^ 2 := by ring
        _ = (1 + √2) ^ n * (2 * (1 + √2) + 1) := by rw [h]
        _ = 2 * (1 + √2) ^ (n + 1) + (1 + √2) ^ n := by ring
    have hrec_minus : (1 - √2) ^ (n + 2) = 2 * (1 - √2) ^ (n + 1) + (1 - √2) ^ n := by
      have h : (1 - √2) ^ 2 = 2 * (1 - √2) + 1 := by
        ring_nf; nlinarith [hsqrt2_sq]
      calc (1 - √2) ^ (n + 2) = (1 - √2) ^ n * (1 - √2) ^ 2 := by ring
        _ = (1 - √2) ^ n * (2 * (1 - √2) + 1) := by rw [h]
        _ = 2 * (1 - √2) ^ (n + 1) + (1 - √2) ^ n := by ring
    field_simp
    linarith [hrec_plus, hrec_minus]

/-- There are infinitely many prime Pell numbers -/
@[category research formally solved using formal_conjectures at "https://en.wikipedia.org/wiki/Pell_number#Primes_and_squares", AMS 11]
theorem infinite_pellNumber_primes : Infinite {n : ℕ | Prime (pellNumber n)} := by
  sorry

-- TODO : Formalise connection between Pell numbers and Pell equation x^2 - 2*y^2 = -1

end PellNumbers
