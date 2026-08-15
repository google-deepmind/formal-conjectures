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

open Nat Int BigOperators

/--
A333565: The coefficients of the ordinary generating function $\frac{1 + 4x}{(1 + x)\sqrt{1 - 8x}}$.
The $n$-th term $a(n)$ is the coefficient of $x^n$, derived via convolution.
Let $b_m = 2^m \binom{2m}{m}$ be the coefficients of $1/\sqrt{1-8x}$, and $d_n = \sum_{k=0}^n (-1)^k b_{n-k}$ be the coefficients of $1/((1+x)\sqrt{1-8x})$. Then $a_n = d_n + 4 d_{n-1}$.
-/
def A333565 (n : ℕ) : ℕ :=
  -- $b_m = 2^m \binom{2m}{m}$ as an integer value. We use ⇑ for coercion from ℕ to ℤ.
  let b_coeff (m : ℕ) : ℤ := (2 ^ m * (2 * m).choose m : ℕ)

  -- $d_n$ coefficient via convolution. The sum goes from 0 to n.
  let d_coeff (n_idx : ℕ) : ℤ :=
    (Finset.range (n_idx + 1)).sum fun k =>
      (-1 : ℤ) ^ k * b_coeff (n_idx - k)

  -- $a_n = d_n + 4 d_{n-1}$. We handle the $d_{-1}=0$ case explicitly.
  let a_n_int : ℤ := d_coeff n + 4 * if n = 0 then 0 else d_coeff (n - 1)

  -- The result is guaranteed to be a natural number.
  a_n_int.toNat

-- The provided simple theorems are kept as placeholders.
theorem a_zero : A333565 0 = 1 := by sorry
theorem a_one : A333565 1 = 7 := by sorry
theorem a_two : A333565 2 = 33 := by sorry
theorem a_three : A333565 3 = 223 := by sorry

/--
We conjecture that this sequence satisfies the stronger congruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 3$ and positive integers $n$ and $k$.
-/
theorem oeis_A333565_conjecture_strong_gauss_congruence (p n k : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hn : n > 0) (hk : k > 0) :
    (A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k) : ℤ)] :=
  by sorry
