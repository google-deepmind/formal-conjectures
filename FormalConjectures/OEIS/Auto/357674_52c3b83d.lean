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

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

theorem a_zero : A357674 0 = 1 := by
  rfl

theorem a_one : A357674 1 = 2187 := by
  rfl

theorem a_two : A357674 2 = 8422734375 := by
  rfl

theorem a_three : A357674 3 = 202402468703748096 := by
  subsingleton

/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  sorry

/--
Conjecture 2: For $r \ge 2$, and all primes $p \ge 3$, $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$.
We interpret $p^{r-1}$ using `Nat.pow p (r - 1)`.
-/
theorem A357674_conjecture_2 (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    A357674 (p ^ r) ≡ A357674 (p ^ (r - 1)) [MOD p ^ (3 * r + 3)] := by
  sorry

/--
Conjecture 3: Let $m$ be a positive integer and set $u(n) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Then the sequence $\{u(n, m)\}$ satisfies the supercongruence $u(p, m) \equiv u(1, m) \pmod{p^5}$
for all primes $p \ge 7$. This is the case $m = 2$.
-/
theorem A357674_conjecture_3 (p m : ℕ) (hp : p.Prime) (hp7 : p ≥ 7) (hm : m ≥ 1) :
    u_A357674 p m ≡ u_A357674 1 m [MOD p ^ 5] := by
  sorry
