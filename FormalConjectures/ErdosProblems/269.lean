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

import FormalConjecturesUtil

/-!
# Erdős Problem 269

*Reference:* [erdosproblems.com/269](https://www.erdosproblems.com/269)
-/

namespace Erdos269
/--
A positive integer $n$ has all its prime factors in the set $P$.
By convention, $1$ satisfies this for any $P$ as it has no prime divisors.
-/
def HasPrimeFactorsIn (P : Set ℕ) (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ∈ P

/--
The infinite, strictly increasing sequence $\{a_0, a_1, \dots\}$ of integers
whose prime factors all belong to $P$.
-/
noncomputable def a (P : Set ℕ) : ℕ → ℕ := Nat.nth <| HasPrimeFactorsIn P

/--
The $n$-th partial least common multiple, $[a_0, \dots, a_{n-1}]$, which is
the LCM of the first $n$ integers in the sequence.
-/
noncomputable def partialLcm (P : Set ℕ) (n : ℕ) : ℕ :=
  -- We take the LCM of `{a P 0, ..., a P n}`.
  (Finset.range n).lcm (a P)

/--
The sum $\sum_{n=1}^\infty \frac{1}{[a_0,\ldots,a_{n - 1}]}$.
-/
noncomputable def series (P : Set ℕ) : ℝ :=  ∑' n, (1 : ℝ) / (partialLcm P n)

/--
Let $P$ be a finite set of primes with $|P| \ge 2$ and let
$\{a_1 < a_2 < \dots\}$ be the set of positive integers whose prime factors
are all in $P$. Is the sum
$$ \sum_{n=1}^\infty \frac{1}{[a_1,\ldots,a_n]} $$
rational?
-/
@[category research open, AMS 11]
theorem erdos_269.variants.rational : answer(sorry) ↔
    ∀ᵉ (P : Finset ℕ) (h : ∀ p ∈ P, p.Prime) (h_card : P.card ≥ 2),
    ∃ (q : ℚ), q = (series (P : Set ℕ)) := by
  sorry

/--
Let $P$ be a finite set of primes with $|P| \ge 2$ and let
$\{a_1 < a_2 < \dots\}$ be the set of positive integers whose prime factors
are all in $P$. Is the sum
$$ \sum_{n=1}^\infty \frac{1}{[a_1,\ldots,a_n]} $$
irrational?
-/
@[category research open, AMS 11]
theorem erdos_269.variants.irrational : answer(sorry) ↔
    ∀ᵉ (P : Finset ℕ) (h : ∀ p ∈ P, p.Prime) (h_card : P.card ≥ 2),
    Irrational (series (P : Set ℕ)) := by
  sorry

/--
This theorem addresses the case where the set of primes $P$ is infinite. In this case the sum is
irrational.
-/
@[category research solved, AMS 11]
theorem erdos_269.variants.infinite (P : Set ℕ) (h : ∀ p ∈ P, p.Prime) (h_inf : P.Infinite) :
  Irrational (series P) := by
  sorry

/--
For three pairwise distinct primes $p$, $q$, $r$ and any cutoff $x$, the least
common multiple of all $\{p,q,r\}$-smooth numbers $p^i q^j r^k \le x$ is the
product of the largest pure powers of $p$, $q$ and $r$ that are at most $x$:
$$ \operatorname{lcm}\{p^i q^j r^k \le x\}
   = p^{\lfloor \log_p x \rfloor} q^{\lfloor \log_q x \rfloor}
     r^{\lfloor \log_r x \rfloor}. $$
The pairwise-distinctness hypotheses are necessary: for $p = q = 2$, $r = 5$
and $x = 100$ the two sides are $1600$ and $102400$.

This is a finite structural identity for the running least common multiple.
It does not establish rationality or irrationality of `series`, and it does
not resolve either open finite-prime variant of this problem.
-/
@[category textbook, AMS 11]
theorem erdos_269.variants.smooth_prefix_lcm
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (x : ℕ) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x :=
  smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr x

end Erdos269
