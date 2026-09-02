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
A141057: Number of Abelian cubes of length $3n$ over an alphabet of size 3.
The formula is $a(n) = \sum_{n_1+n_2+n_3=n, n_i \ge 0} \left(\frac{n!}{n_1! n_2! n_3!}\right)^3$.
This sum is computed via the identity $\binom{n}{n_1, n_2, n_3} = \binom{n}{n_1} \binom{n-n_1}{n_2}$:
$$a(n) = \sum_{n_1=0}^n \sum_{n_2=0}^{n-n_1} \left(\binom{n}{n_1} \binom{n-n_1}{n_2}\right)^3$$
-/
def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3


theorem a_zero : A141057 0 = 1 := by
  simp [A141057, choose_zero_right, tsub_zero]

theorem a_one : A141057 1 = 3 := by
  sorry

theorem a_two : A141057 2 = 27 := by
  sorry

theorem a_three : A141057 3 = 381 := by
  sorry


/--
Conjecture: the supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
hold for primes $p \ge 5$ and positive integers $n$ and $k$.
The note regarding extending the sequence to negative $n$ is omitted from the formal statement,
which focuses on the main claim for $n \in \mathbb{N}^+$.
-/
theorem oeis_a141057_supercongruence_conjecture (p k n : ℕ)
    (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (h_n_pos : 1 ≤ n) :
    (A141057 (n * p ^ k) : ℤ) ≡ A141057 (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k))] := by
  sorry
