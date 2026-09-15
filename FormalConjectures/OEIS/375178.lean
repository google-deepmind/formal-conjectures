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
# Sum of cubed binomial coefficients $\sum_{k=0}^{n-1} \binom{n+k-1}{k}^3$

The sequence is defined by
$$a(n) = \sum_{k=0}^{n-1} \binom{n+k-1}{k}^3$$

*References:*
- [A375178](https://oeis.org/A375178)
-/

open Nat Finset

namespace OeisA375178

/--
The sequence $a(n) = \sum_{k=0}^{n-1} \binom{n+k-1}{k}^3$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (multichoose n k) ^ 3

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by simp [a, multichoose_eq]

@[category test, AMS 11]
theorem a_2 : a 2 = 9 := by simp [a, multichoose_eq, sum_range_succ]

@[category test, AMS 11]
theorem a_3 : a 3 = 244 := by simp [a, multichoose_eq, sum_range_succ]; decide

@[category test, AMS 11]
theorem a_4 : a 4 = 9065 := by simp [a, multichoose_eq, sum_range_succ]; decide

/--
The generalized sequence $b_m(n) = \sum_{k = 0}^{n-1} \binom{n+k-1}{k}^{2m+1}$.
-/
noncomputable
def b (m : ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (multichoose n k) ^ (2 * m + 1)

/--
Conjecture: for a positive integer m, define a sequence $b_m(n)$ as
$b_m(n) = \sum_{k = 0}^{n-1} \binom{n+k-1}{k}^{2m+1}$.
We conjecture that the supercongruence $b_m(p) \equiv 1 \pmod{p^{2m+3}}$ holds
for all primes $p \ge 2m + 5$, and for $r \ge 2$, the supercongruence
$b_m(p^r) \equiv b_m(p^{r-1}) \pmod{p^{3r+2m+1}}$ also holds for all primes $p \ge 2m + 5$.
-/
@[category research open, AMS 11]
theorem conjecture_2a (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : Nat.Prime p) :
  p ≥ 2 * m + 5 → b m p ≡ 1 [MOD p ^ (2 * m + 3)] :=
by sorry

/--
For $r \ge 2$, the supercongruence
$b_m(p^r) \equiv b_m(p^{r-1}) \pmod{p^{3r+2m+1}}$ holds for all primes $p \ge 2m + 5$.
-/
@[category research open, AMS 11]
theorem conjecture_2b (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : 2 ≤ r) (p : ℕ) (hp : Nat.Prime p) :
  p ≥ 2 * m + 5 → b m (p^r) ≡ b m (p^(r - 1)) [MOD p ^ (3 * r + 2 * m + 1)] :=
by sorry

end OeisA375178
