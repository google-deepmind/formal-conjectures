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
# Alternating sum $\sum_{k=0}^{n-1} (-1)^{n+k+1} \binom{n}{k} \binom{n+k-1}{k}^2$

The sequence is defined by
$$a(n) = \sum_{k=0}^{n-1} (-1)^{n+k+1} \binom{n}{k} \binom{n+k-1}{k}^2$$

*References:*
- [A361714](https://oeis.org/A361714)
-/
open Nat Int Finset

namespace OeisA361714

/--
The sequence $a(n) = \sum_{k=0}^{n-1} (-1)^{n+k+1} \binom{n}{k} \binom{n+k-1}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ k ∈ range n,
    (
      (-1 : ℤ) ^ (n + k + 1) *
      (n.choose k : ℤ) *
      ((Nat.choose (n + k - 1) k : ℤ) ^ 2)
    )
  ).natAbs

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 7 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 82 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1063 := by rfl

/--
The supercongruence $a(p) \equiv a(1) \pmod{p^5}$ holds for all primes $p \ge 7$.
-/
@[category research open, AMS 11]
theorem conjecture_1 {p : ℕ} (hp : p.Prime) (hp_ge_7 : 7 ≤ p) :
  (a p : ℤ) ≡ a 1 [ZMOD (p ^ 5 : ℤ)] :=
  by sorry

/--
For $r \ge 2$, the supercongruence
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ holds for all primes $p \ge 7$.
-/
@[category research open, AMS 11]
theorem conjecture_2 {p r : ℕ} (hp : p.Prime) (hp_ge_7 : 7 ≤ p) (hr_ge_2 : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℤ)] :=
  by sorry

end OeisA361714
