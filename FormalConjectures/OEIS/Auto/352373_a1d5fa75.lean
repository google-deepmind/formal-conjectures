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

open scoped BigOperators Nat Finset Int

/--
A352373: $a(n) = [x^n] \left( \frac{1}{(1 - x)^2(1 - x^2)} \right)^n$ for $n \ge 1$.
The sequence is explicitly given by the combinatorial sum:
$$a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} \binom{3n-2k-1}{n-2k} \binom{n+k-1}{k}$$
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let n' := n
  Finset.sum (Finset.range (n' / 2 + 1)) fun k =>
    let term1_top := 3 * n' - 2 * k - 1
    let term1_bot := n' - 2 * k
    let term2_top := n' + k - 1
    let term2_bot := k
    (term1_top.choose term1_bot) * (term2_top.choose term2_bot)

lemma a_one : a 1 = 2 := by rfl
lemma a_two : a 2 = 12 := by rfl
lemma a_three : a 3 = 74 := by rfl
lemma a_four : a 4 = 484 := by rfl

/--
A352373 Conjecture: the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))
hold for all primes p >= 5 and positive integers n and k.
-/
theorem oeis_a352373_supercongruence :
  ∀ (p : ℕ) (hp_prime : p.Prime) (hp_ge_5 : p ≥ 5),
  ∀ (n : ℕ) (hn_pos : 0 < n),
  ∀ (k : ℕ) (hk_pos : 0 < k),
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] :=
by sorry
