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
The sequence $\beta(k) = A005258(k) = \sum_{j=0}^k \binom{k}{j}^2 \binom{k+j}{j}$.
-/
def A329478_beta (k : ℕ) : ℚ :=
  (Finset.range (k + 1)).sum fun j => ((k.choose j : ℚ) ^ 2 * ((k + j).choose j : ℚ))

/--
$t(k)$ is the coefficient of $x^k$ in the expansion of $(x^2+4x-1)^k$.
Its combinatorial formula is $t(k) = \sum_{i=0}^{\lfloor k/2 \rfloor} (-1)^i \binom{k}{i} \binom{k-i}{i} 4^{k-2i}$.
-/
def A329478_t (k : ℕ) : ℚ :=
  (Finset.range (k / 2 + 1)).sum fun i =>
    let choose_vals : ℚ := (k.choose i : ℚ) * ((k - i).choose i : ℚ)
    let four_pow : ℚ := (4 : ℚ) ^ (k - 2 * i)
    let sign : ℚ := ((-1) : ℚ) ^ i
    sign * choose_vals * four_pow

/--
A329478: $a(n) = \frac{1}{2n} \sum_{k=0}^{n-1}(-1)^k(15k+8)\beta(k)t(k)$.
-/
noncomputable def A329478 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator := Finset.sum (Finset.range n) fun k =>
      let k_q : ℚ := k
      let sign_k : ℚ := (-1) ^ k
      let factor : ℚ := 15 * k_q + 8
      sign_k * factor * (A329478_beta k) * (A329478_t k)

    let denom : ℚ := 2 * (n : ℚ)
    numerator / denom

/--
Conjecture 1: (i) a(n) is an integer for each n > 0. Moreover, a(n) is odd if and only if n is a positive power of two.
This formalizes the claim that for $n > 0$, $A329478(n)$ is an integer, and its parity matches whether $n$ is a power of two.
When $q$ is an integer rational number, its value is given by its numerator, $q.num$.
-/
theorem oeis_329478_conjecture_0 (n : ℕ) (hn : 0 < n) :
  (A329478 n).isInt ∧
  (Odd (A329478 n).num ↔ Nat.isPowerOfTwo n) := by sorry
