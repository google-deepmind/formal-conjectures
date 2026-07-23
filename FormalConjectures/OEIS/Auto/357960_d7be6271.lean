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
A357960: $a(n) = A005259(n-1)^5 \cdot A005258(n)^6$.
The sequence is defined by the combinatorial formula:
$$a(n) = \left( \sum_{k = 0}^{n-1} \binom{n-1}{k}^2 \binom{n+k-1}{k}^2 \right)^5 \cdot \left( \sum_{k = 0}^{n} \binom{n}{k}^2 \binom{n+k}{k} \right)^6$$
-/
def a (n : ℕ) : ℕ :=
  let N := n - 1
  ( (range n).sum fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2 ) ^ 5 *
  ( (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ) ^ 6


theorem a_one : a 1 = 729 := by
  rfl

theorem a_two : a 2 = 147018378125 := by
  rfl

theorem a_three : a 3 = 20917910914764786689697 := by
  rfl

theorem a_four : a 4 = 24148107115850058575342740485778125 := by
  rfl

/--
Conjecture 1 from OEIS A357960:
$a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem oeis_A357960_conjecture_1 (p : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) :
    a p ≡ a 1 [MOD p ^ 5] := by
  sorry

/--
Conjecture 2 from OEIS A357960:
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and for all primes $p \ge 3$.
-/
theorem oeis_A357960_conjecture_2 (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r + 3)] := by
  sorry
