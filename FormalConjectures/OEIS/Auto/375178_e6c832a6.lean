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

/--
A375178: $a(n) = \sum_{k = 0}^{n-1} \binom{n+k-1}{k}^3$.
This is equivalent to a sum of cubed multichoose coefficients: $\sum_{k=0}^{n-1} \left(\left(\!\binom{n}{k}\!\right)\right)^3$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (Nat.multichoose n k) ^ 3

/--
The generalized sequence $b_m(n) = \sum_{k = 0}^{n-1} \binom{n+k-1}{k}^{2m+1}$.
-/
noncomputable
def b (m : ℕ) (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (Nat.multichoose n k) ^ (2 * m + 1)

/--
Conjecture: for a positive integer m, define a sequence $b_m(n)$ as
$b_m(n) = \sum_{k = 0}^{n-1} \binom{n+k-1}{k}^{2m+1}$.
We conjecture that the supercongruence $b_m(p) \equiv 1 \pmod{p^{2m+3}}$ holds
for all primes $p \ge 2m + 5$, and for $r \ge 2$, the supercongruence
$b_m(p^r) \equiv b_m(p^{r-1}) \pmod{p^{3r+2m+1}}$ also holds for all primes $p \ge 2m + 5$.
-/
theorem oeis_375178_conjecture_2a (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : Nat.Prime p) :
  p ≥ 2 * m + 5 → b m p ≡ 1 [MOD p ^ (2 * m + 3)] :=
by sorry

theorem oeis_375178_conjecture_2b (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : 2 ≤ r) (p : ℕ) (hp : Nat.Prime p) :
  p ≥ 2 * m + 5 → b m (p^r) ≡ b m (p^(r - 1)) [MOD p ^ (3 * r + 2 * m + 1)] :=
by sorry
