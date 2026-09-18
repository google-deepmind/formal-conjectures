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
# Representations of $n$ using prime pairs with prime gaps of $6$

Number of ways to write $n = p + q(3 - (-1)^n)/2$ with $p > q$ and $p, q, p - 6, q + 6$ all prime.

*References:*
- [A219055](https://oeis.org/A219055)
-/

namespace OeisA219055

/-- Number of ways to write $n = p + q(3 - (-1)^n)/2$ with $p > q$ and $p, q, p - 6, q + 6$ all
prime. -/
def a (n : ℕ) : ℕ :=
  (Finset.range n).filter (fun q : ℕ =>
    ((1 + n % 2) + 1) * q < n ∧
    q.Prime ∧
    (q + 6).Prime ∧
    (n - (1 + n % 2) * q).Prime ∧
    (n - (1 + n % 2) * q - 6).Prime
  ) |>.card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_16 : a 16 = 1 := by decide

@[category test, AMS 11]
theorem a_18 : a 18 = 2 := by decide

/--
Conjecture: $a(n) > 0$ for all even $n > 8012$ and odd $n > 15727$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)) : a n > 0 := by
  sorry

/--
Conjecture: For any two multiples $d_1$ and $d_2$ of
$6$, all sufficiently large integers $n$ can be written as $p + q(3 - (-1)^n)/2$ with $p > q$ and
$p, q, p - d_1, q + d_2$ all prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture2 (d₁ d₂ : ℤ) (hd₁ : 6 ∣ d₁) (hd₂ : 6 ∣ d₂) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ p q p' q' : ℕ, q < p ∧ p.Prime ∧ q.Prime ∧ p'.Prime ∧ q'.Prime ∧
        (p : ℤ) - d₁ = p' ∧ (q : ℤ) + d₂ = q' ∧ n = p + (1 + n % 2) * q := by
  sorry

end OeisA219055
