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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 930

*Reference:* [erdosproblems.com/930](https://www.erdosproblems.com/930)
-/

open Finset

namespace Erdos930

/--
$n$ is a perfect power if there exist natural numbers $m$ and $l$
such that $1 < m$, $1 < l$, and $m^l = n$.
-/
def PerfectPower (n : ℕ) : Prop :=
  ∃ m l, 1 < m ∧ 1 < l ∧ m^l = n

/--
Is it true that, for every $r$, there is a $k$ such that
if $I_1,\ldots,I_r$ are disjoint intervals of consecutive integers,
all of length at least $k$, then
$$
  \prod_{1\leq i\leq r}\prod_{m\in I_i}m
$$
is not a perfect power?
-/
@[category research open, AMS 11]
theorem erdos_930 :
  ∀ r, ∃ k, ∀ (I : Fin r → Finset ℕ),
    (∀ i j : Fin r, i ≠ j → Disjoint (I i) (I j)) →
      (∀ i : Fin r, k ≤ (I i).card ∧ ∃ a, I i = Ico a (a + (I i).card)) →
        ¬ PerfectPower (∏ i : Fin r, ∏ m ∈ I i, m) := by
  sorry

/--
$p$ is the least prime satisfying $k \le p$
if for any other prime $q$, $k \le q$ implies $p \le q$.
-/
def leastPrime (k p : ℕ) : Prop :=
  p.Prime ∧ k ≤ p ∧ ∀ q, k ≤ q ∧ q.Prime → p ≤ q

/--
$n$ is greater than the least prime $p$ satisfying $k \le p$
-/
def gtLeastPrime (k n : ℕ) : Prop :=
  ∀ p, leastPrime k p → p < n

/--
Let $k$, $l$, $n$ be integers such that $k \ge 3$, $l \ge 2$ and $n + k \ge p^{(k)}$,
where $p^{(k)}$ is the least prime satisfying $p^{(k)} \ge k$.
Then there is a prime $p \ge k$ for which $\alpha_p \not\equiv 0 \pmod{1}$,
where $\alpha_p$ is the power of $p$ dividing $(n + 1) \ldots (n + k)$.

Theorem 2 from [ErSe75].

[ErSe75] Erdős, P. and Selfridge, J. L., The product of consecutive integers is never a power. Illinois J. Math. (1975), 292-301.
-/
@[category research solved, AMS 11]
theorem erdos_930.variant.consecutive_strong :
  ∀ k l n, 3 ≤ k → 2 ≤ l → gtLeastPrime k (n + k) →
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  sorry

/--
Erdos and Selfridge [ErSe75] proved that the product of
consecutive integers is never a power (establishing the case $r=1$).

Theorem 1 from [ErSe75].

It is implied from `erdos_930.variant.consecutive_strong`.

[ErSe75] Erdős, P. and Selfridge, J. L., The product of consecutive integers is never a power. Illinois J. Math. (1975), 292-301.
-/
@[category research solved, AMS 11]
theorem erdos_930.variant.consecutive_integers :
  ∀ n k, 0 ≤ n → 2 ≤ k →
    ¬ PerfectPower (∏ m ∈ Icc (n + 1) (n + k), m) := by
  sorry

end Erdos930
