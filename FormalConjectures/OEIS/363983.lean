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
# Alternating sum of triple binomial products

The sequence is defined by
$$a(n) = \sum_{k=\lfloor(n+1)/2\rfloor}^n (-1)^{n+k} \binom{n}{k} \binom{n+k-1}{k} \binom{2k}{n}$$

*References:*
- [A363983](https://oeis.org/A363983)
-/
open Nat Finset Int

namespace OeisA363983

/--
The sequence $a(n) = \sum_{k=\lfloor(n+1)/2\rfloor}^n (-1)^{n+k} \binom{n}{k} \binom{n+k-1}{k}
\binom{2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ range (n + 1),
    -- The expression must result in ℤ due to the alternating sign.
    let sign_factor : ℤ := (-1) ^ (n + k)
    -- Binomial coefficients (Nat.choose) are implicitly coerced to ℤ for multiplication.
    -- (n + k - 1).choose k is written as ((n + k).pred.choose k) in Mathlib's Nat.choose syntax.
    let term_val : ℤ := (n.choose k) * ((n + k).pred.choose k) * ((2 * k).choose n)
    sign_factor * term_val
  ).toNat

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 14 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 128 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1310 := by rfl

/--
The Franel numbers satisfy the supercongruences
$A000172(n p^r) \equiv A000172(n p^{r-1}) \pmod{p^{3r}}$
for all primes $p \ge 5$ and positive integers $n$ and $r$.
The present sequence satisfies the same supercongruences.
-/
@[category research open, AMS 11]
theorem supercongruence (p n r : ℕ) (hp : p.Prime) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r
> 0) :
  (a (n * p ^ r) : ℤ) ≡ a (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry

end OeisA363983
