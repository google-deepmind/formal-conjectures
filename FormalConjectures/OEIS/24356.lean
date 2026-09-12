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

import FormalConjecturesUtil

/-!
# Determinant of Hankel matrix of the first $2n-1$ prime numbers

The determinant of the $n \times n$ Hankel matrix whose entries are the first $2n-1$ prime numbers.
The matrix $M$ has entries $M_{i, j} = p_{i+j}$ for $i, j \in \{0, \dots, n-1\}$,
where $p_k = \mathrm{Nat.nth\;Nat.Prime} (k)$ is the $k$-th prime starting at $p_0=2$.
$a(0)=1$ by convention.

*References:*
- [A024356](https://oeis.org/A024356)-/

namespace OeisA24356

/-- The determinant of the $n \times n$ Hankel matrix of primes. -/
noncomputable def a (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun (i j : Fin n) ↦ (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  simp [a]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  simp [a, Nat.nth_prime_zero_eq_two]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  simp [a, Matrix.det_fin_two, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-- Value of the sequence `a` at 4. This records the zero whose uniqueness is conjectured below. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  unfold a
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have h5 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count hp13
  have h6 : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count hp17
  have hM :
      (Matrix.of fun (i j : Fin 4) ↦ (Nat.nth Nat.Prime (i.val + j.val) : ℤ)) =
        !![(2 : ℤ), 3, 5, 7; 3, 5, 7, 11; 5, 7, 11, 13; 7, 11, 13, 17] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
        Nat.nth_prime_four_eq_eleven, h5, h6]
  rw [hM]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (v := ![(6 : ℤ), -3, -2, 1]) (i := 0)
  · decide
  · norm_num [nonZeroDivisors]

/--
"I conjecture that $a(4)$ is the only zero. - _Jon Perry_, Mar 22 2004"

Stated as a biconditional: the claim that $a(4)$ is *the only* zero asserts both that $a(4) = 0$
and that no other index vanishes. A bare implication `a n = 0 → n = 4` would be satisfied
vacuously by a sequence with no zero at all. The existence direction is certified by `a_4`; the
uniqueness direction is the open part. -/
@[category research open, AMS 11 15]
theorem conjecture : ∀ n : ℕ, a n = 0 ↔ n = 4 := by
  sorry

end OeisA24356
