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
# Ratio of product of GCDs to product of factorials of floor divisions

$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$

*References:*
- [A129365](https://oeis.org/A129365)
-/

namespace OeisA129365

/-- $a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$. -/
def a (n : ℕ) : ℚ :=
  let num : ℚ := (Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k
  let den : ℚ := (Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k
  num / den

/-- Sequence A004125: sum of remainders $n \bmod k$ for $1 \le k \le n$. -/
def b (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (n % k)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide +native

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide +native

/--
Conjecture (1): $a(n)$ is always an integer (the denominator divides the numerator).
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 0 < n) :
    ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ∣
      ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) := by
  sorry

/--
Conjecture (2): If $p$ is a prime, then $p \mid a(n)$ if and only if $p \le n/3$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    (∃ m : ℕ, a n = m ∧ p ∣ m) ↔ p ≤ n / 3 := by
  sorry

/--
Conjecture (3): For each positive integer $n$, prime $p$, and $0 \le k < p$,
$\mathrm{ord}_p(a(np)) = \mathrm{ord}_p(a(np + k))$.
-/
@[category research open, AMS 11]
theorem conjecture3 (n p k : ℕ) (hn : 0 < n) (hp : p.Prime) (hk : k < p) :
    padicValRat p (a (n * p)) = padicValRat p (a (n * p + k)) := by
  sorry

/--
Conjecture (4): Let $b(n) = \mathrm{A004125}(n) = \sum_{k=1}^n (n \bmod k)$. Then
$\mathrm{ord}_p(a(np)) = \sum_{i \ge 0} b(\lfloor n/p^i \rfloor)$.
-/
@[category research open, AMS 11]
theorem conjecture4 (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ) := by
  sorry

end OeisA129365

