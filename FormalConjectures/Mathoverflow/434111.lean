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
# Are prime numbers among sums of prime numbers distributed as $\frac n{2\ln(n)}$?

*Reference:*

[mathoverflow.net/questions/434111](https://mathoverflow.net/questions/434111/are-prime-numbers-among-sums-of-prime-numbers-distributed-as-frac-n2-lnn)

[Me18] Meštrović, R., *Curious Conjectures on the Distribution of Primes
Among the Sums of the First `2n` Primes*, [arXiv:1804.04198](https://arxiv.org/abs/1804.04198)
(2018), Conjecture 3.3.
-/

namespace MathOverflow434111

open Nat Filter Topology Asymptotics

/-- $S_n$ is the sum of the first `n` primes, i.e. $S_n=p_1+\dots+p_n$, $1$-indexed,
matching the MathOverflow question. -/
noncomputable def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, nth Nat.Prime k

/-- $\pi_n$ counts how many of $S_1,S_2,\dots,S_n$ are themselves prime,
i.e. $\pi_n$ as used on MathOverflow (compare to $\pi_n$ in [Me18, Conjecture 3.3],
which instead ranges over $S_2,S_4,\dots,S_{2n}$). -/
noncomputable def piRestricted (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Nat.Prime (S k))).card

/-- The conjecture claims that $\pi_n\sim\frac n{2\ln(n)}$.

In other words, primes are distributed among the much sparser sequence $(S_n)_n$
with essentially the same density as in the positive integers, up to a factor of $2$.

[MathOverflow 434111](https://mathoverflow.net/questions/434111/are-prime-numbers-among-sums-of-prime-numbers-distributed-as-frac-n2-lnn).

[Me18] Meštrović, R., *Curious Conjectures on the Distribution of Primes
Among the Sums of the First `2n` Primes*, [arXiv:1804.04198](https://arxiv.org/abs/1804.04198)
(2018).
-/
@[category research open, AMS 11]
theorem restricted_prime_number_theorem :
    answer(sorry) ↔ ((fun n : ℕ => (piRestricted n : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ) / (2 * Real.log n))) := by
  sorry

/--
Meštrović's original formulation [Me18, Conjecture 3.3]: the sequence of sums of the
first $2m$ primes satisfies the Restricted Prime Number Theorem, $\pi(m, (S_{2m})) \sim \frac{m}{\ln m}$.
-/
@[category research open, AMS 11]
theorem restricted_prime_number_theorem.variants.even_subsequence :
    answer(sorry) ↔
      ((fun m : ℕ => (((Finset.Icc 1 m).filter (fun k => Nat.Prime (S (2 * k)))).card : ℝ)) ~[atTop]
        (fun m : ℕ => (m : ℝ) / Real.log m)) := by
  sorry

end MathOverflow434111
