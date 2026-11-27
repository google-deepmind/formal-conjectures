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
# Product of powers of Apéry numbers $A(n-1)^5 B(n)^6$

The sequence is defined by $a(n) = A(n-1)^5 B(n)^6$, where $A(n)$ are the Apéry numbers for
$\zeta(3)$
(A005259) and $B(n)$ are the Apéry numbers for $\zeta(2)$ (A005258).

*References:*
- [A357960](https://oeis.org/A357960)
-/
open Nat Finset

namespace OeisA357960

/--
The sequence $a(n) = A(n-1)^5 B(n)^6$ for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  let N := n - 1
  ( ∑ k ∈ range n, (N.choose k) ^ 2 * ((N + k).choose k) ^ 2 ) ^ 5 *
  ( ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * ((n + k).choose k) ) ^ 6

@[category test, AMS 11]
theorem a_1 : a 1 = 729 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 147018378125 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 20917910914764786689697 := by
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 24148107115850058575342740485778125 := by
  rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 79477722547796770983047586179643766765851375729 := by rfl

/--
$a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) :
    a p ≡ a 1 [MOD p ^ 5] := by
  sorry

/--
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and for all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_2 (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r + 3)] := by
  sorry

end OeisA357960
