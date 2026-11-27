/-
Copyright 2025 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 677

*References:*
- [erdosproblems.com/677](https://www.erdosproblems.com/677)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math. Acad. Sci.
  Hungar. (1979), 71-80.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437. Problem B35.
-/

@[expose] public section

namespace Erdos677

open Finset

/--
Erdős expected very few solutions for $M(n, k) = M(m, l)$, where $m \geq n + k$ and $l > 1$.
The only solutions he knew were the following.
-/
@[category test, AMS 11]
lemma lcmInterval_eq_example1 : lcmInterval 4 3 = lcmInterval 13 2 ∧
                                lcmInterval 3 4 = lcmInterval 19 2 := by decide

/--
Denote by $M(n, k)$ the least common multiple of the finite set $\{n+1, \dotsc, n+k\}$.
Is it true that for all $m \geq n + k$, we get $M(m, k) \neq M(n, k)$?
-/
@[category research open, AMS 11]
theorem erdos_677 :
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k := by
  sorry

/--
The Thue-Siegel theorem implies that, for fixed $k$, there are only finitely many $m, n$ with
$m \geq n + k$ and $M(n, k) = M(m, k)$.
-/
@[category research solved, AMS 11]
theorem erdos_677.variants.finite (k : ℕ) (hk : 0 < k) :
    {(m, n) | n + k ≤ m ∧ lcmInterval m k = lcmInterval n k}.Finite := by
  sorry

/--
In general, how many solutions does $M(n, k) = M(m, l)$ have when $m \geq n + k$ and $l > 1$?
Erdős expected very few, and none when $l \geq k$. This is the second expectation: there are no
solutions with $l \geq k$.
-/
@[category research open, AMS 11]
theorem erdos_677.variants.length_le :
    ∀ (m n k l : ℕ), 0 < k → 1 < l → k ≤ l → n + k ≤ m →
      lcmInterval n k ≠ lcmInterval m l := by
  sorry

/--
Two more solutions of $M(n, k) = M(m, l)$ with $m \geq n + k$ and $l > 1$, besides the two in
`lcmInterval_eq_example1`: $M(8, 4) = M(43, 2) = 1980$ and
$M(153, 3) = M(1363, 2) = 1861860$. Both have $l < k$, in line with `erdos_677.variants.length_le`.
-/
@[category test, AMS 11]
lemma lcmInterval_eq_example2 : lcmInterval 8 4 = lcmInterval 43 2 ∧
                                lcmInterval 153 3 = lcmInterval 1363 2 := by decide

/--
Erdős [Er79d] conjectured the stronger fact that, aside from a finite number of exceptions, if
$k > 2$ and $m \geq n + k$ then $\prod_{i \leq k}(n + i)$ and $\prod_{i \leq k}(m + i)$ cannot
have the same set of prime factors.

We read "a finite number of exceptions" as finitely many triples $(k, m, n)$. Compare
`Erdos931.erdos_931`, which asks for finitely many pairs for each fixed pair of lengths.
-/
@[category research open, AMS 11]
theorem erdos_677.variants.prime_factors :
    {(k, m, n) | 2 < k ∧ n + k ≤ m ∧
      (∏ i ∈ Finset.Icc 1 k, (n + i)).primeFactors =
      (∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors}.Finite := by
  sorry

/--
Exceptions to `erdos_677.variants.prime_factors` do exist: $3 \cdot 4 \cdot 5$ and
$8 \cdot 9 \cdot 10$ both have the set of prime factors $\{2, 3, 5\}$.
-/
@[category test, AMS 11]
lemma primeFactors_eq_example :
    (∏ i ∈ Finset.Icc 1 3, (2 + i)).primeFactors =
    (∏ i ∈ Finset.Icc 1 3, (7 + i)).primeFactors := by
  norm_num [Finset.prod_Icc_succ_top]
  norm_num +decide [Nat.primeFactors, Nat.primeFactorsList]
