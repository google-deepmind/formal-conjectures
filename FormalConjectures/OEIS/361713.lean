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
# Sum of products $\binom{n}{k}^2 \binom{n+k-1}{k}^2$

The sequence is defined by
$$a(n) = \sum_{k=0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}^2$$

*References:*
- [A361713](https://oeis.org/A361713)
-/
open Finset Nat

namespace OeisA361713

/--
The sequence $a(n) = \sum_{k=0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}^2$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 17 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 406 := by
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 10257 := by rfl

/--
The supercongruence $a(p) \equiv a(1) \pmod{p^5}$ holds for all primes $p \ge 7$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    a p ≡ a 1 [MOD p ^ 5] := by
  sorry

/--
For $r \ge 2$, the supercongruence $a(p^r) \equiv a(p^{r-1}) \pmod{p^{4r+1}}$ holds for all
primes $p \ge 7$.
-/
@[category research open, AMS 11]
theorem conjecture_2 (p r : ℕ) :
  p.Prime →
  p ≥ 7 →
  r ≥ 2 →
  a (p ^ r) ≡ a (p ^ (r - 1)) [MOD (p ^ (4 * r + 1))] :=
by sorry

end OeisA361713
