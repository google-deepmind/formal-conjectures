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
# A binomial coefficient sum

A binomial coefficient sum:
$$a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \left( \binom{n}{k} - \binom{n}{k-1} \right)^3$$
where $\binom{n}{-1} = 0$.

*References:*
- [A003161](https://oeis.org/A003161)-/

namespace OeisA3161

/-- A binomial coefficient sum:
$a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} (\binom{n}{k} - \binom{n}{k-1})^3$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    let diff : ℤ := (n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))
    (diff ^ 3).toNat

/-- Auxiliary sequence $b(n) = a(2n-1)$. -/
def b (n : ℕ) : ℕ :=
  a (2 * n - 1)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 9 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 36 := by rfl

/--
Let $b(n) = a(2n-1)$. Then the supercongruence $b(n p^k) \equiv b(n p^{k-1}) \pmod{p^{3k}}$
holds for positive integers $n$ and $k$ and all primes $p \ge 5$.
- Zhi-Wei Sun, Nov 16 2019-/
@[category research open, AMS 11]
theorem conjecture (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OeisA3161
