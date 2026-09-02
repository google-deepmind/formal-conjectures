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

open Nat BigOperators Finset

/--
A352275: $a(0) = 1$ and
$$a(n) = \sum_{k = 0}^{2n} \frac{n}{n + 2k} \binom{n + 2k}{k} \text{ for } n \ge 1.$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (2 * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 4 := by
  norm_num[a]
  norm_num+decide only[Finset.sum_range_succ,Nat.choose]

theorem a_two : a 2 = 64 := by
  inhabit ℝ
  delta a
  norm_num+decide only[Nat.choose,if_true, Finset.sum_range_succ, if_false]

theorem a_three : a 3 = 1429 := by
  delta a
  norm_num+decide only[Nat.choose, if_false, true, Finset.sum_range_succ]

/--
More generally, for $m$ a positive integer, define a sequence $u_m$ by setting
$$u_m(n) = \sum_{k = 0}^{m n} \frac{n}{n + 2k} \binom{n + 2k}{k} \text{ for } n \ge 1.$$
We set $u_m(0) = 1$ to match the sequence $A352275 = u_2$.
-/
noncomputable def u (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (m * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat

/--
oeis_352275_conjecture_2:
Then we conjecture that each sequence $u_m$ satisfies the above supercongruences.
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$ hold for primes $p \ge 5$ and positive integers $n$ and $r$.
This is equivalent to: $u_m(n p^r) \equiv u_m(n p^{r-1}) \pmod{p^{3r}}$ holds for primes $p \ge 5$ and positive integers $m, n, r$.
-/
theorem u_m_supercongruence_conjecture (m n r : ℕ) (hm : m > 0) (hn : n > 0) (hr : r > 0)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (u m (n * p ^ r) : ℤ) ≡ (u m (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℤ)] := by
  sorry
