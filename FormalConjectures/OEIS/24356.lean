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

/--
"I conjecture that $a(4)$ is the only zero. - _Jon Perry_, Mar 22 2004"-/
@[category research open, AMS 11 15]
theorem conjecture : ∀ n : ℕ, a n = 0 → n = 4 := by
  sorry

end OeisA24356
