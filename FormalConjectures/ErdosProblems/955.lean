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

/-!
# Erdős Problem 955

*References:*
- [erdosproblems.com/955](https://www.erdosproblems.com/955)
- [EGPS90] Erdős, P. and Granville, A. and Pomerance, C. and Spiro, C., On the normal behavior of
  the iterates of some arithmetic functions. Analytic number theory (Allerton Park, IL, 1989)
  (1990), 165-204.
- [Er73b] Erdős, P., Über die Zahlen der Form $\sigma(n) - n$ und $n - \phi(n)$. Elem. Math.
  (1973), 83--86.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
- [PPT18] Pollack, Paul and Pomerance, Carl and Thompson, Lola, Divisor-sum fibers. Mathematika
  (2018), 330--342.
- [Po14b] Pollack, Paul, Some arithmetic properties of the sum of proper divisors and the sum of
  prime divisors. Illinois J. Math. (2014), 125--147.
- [Tr15] Troupe, Lee, On the number of prime factors of values of the sum-of-proper-divisors
  function. J. Number Theory (2015), 120--135.
- [Tr20] Troupe, Lee, Divisor sums representable as the sum of two squares. Proc. Amer. Math. Soc.
  (2020), 4189--4202.
-/

open Nat Filter
open scoped ArithmeticFunction Topology Classical

namespace Erdos955

/--
Let $s(n)=\sigma(n)-n=\sum_{\substack{d\mid n\\ d<n}}d$ be the sum of proper divisors function.
-/
def s (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n

/--
If $A\subset \mathbb{N}$ has density $0$ then $s^{-1}(A)$ must also have density $0$.

A conjecture of Erdős, Granville, Pomerance, and Spiro [EGPS90].
-/
@[category research open, AMS 11]
theorem erdos_955 :
    answer(sorry) ↔
      ∀ A : Set ℕ,
        Tendsto (fun n ↦ (count A n : ℝ) / n) atTop (𝓝 0) →
        Tendsto (fun n ↦ (count { x | s x ∈ A } n : ℝ) / n) atTop (𝓝 0) := by
  sorry

/--
It is possible for $s(A)$ to have positive density even if $A$ has zero density (for example
taking $A$ to be the product of two distinct primes).
-/
@[category research solved, AMS 11]
theorem erdos_955.variants.positive_density :
    ∃ A : Set ℕ,
      Tendsto (fun n ↦ (count A n : ℝ) / n) atTop (𝓝 0) ∧
      (∃ d > 0, Tendsto (fun n ↦ (count (s '' A) n : ℝ) / n) atTop (𝓝 d)) := by
  sorry

/--
Erdős [Er73b] proved that there are sets $A$ of positive density such that $s^{-1}(A)$ is empty.
-/
@[category research solved, AMS 11]
theorem erdos_955.variants.empty_preimage :
    ∃ A : Set ℕ,
      (∃ d > 0, Tendsto (fun n ↦ (count A n : ℝ) / n) atTop (𝓝 d)) ∧
      { x | s x ∈ A } = ∅ := by
  sorry

/--
Pollack [Po14b] has shown that this is true if $A$ is the set of primes.
-/
@[category research solved, AMS 11]
theorem erdos_955.variants.pollack_primes :
    Tendsto (fun n ↦ (count { x | Nat.Prime (s x) } n : ℝ) / n) atTop (𝓝 0) := by
  sorry

/--
Troupe [Tr15] has shown that this is true if $A$ is the set of integers with unusually many prime
factors.
-/
@[category research solved, AMS 11]
theorem erdos_955.variants.troupe_unusually_many_prime_factors :
    ∀ ε > 0, Tendsto (fun n ↦ (count { x | (1 + ε) * Real.log (Real.log (s x)) <
      (ArithmeticFunction.cardDistinctFactors (s x) : ℝ) } n : ℝ) / n) atTop (𝓝 0) := by
  sorry

/--
Troupe [Tr20] has also shown this is true if $A$ is the set of integers which are the sum of two
squares.
-/
@[category research solved, AMS 11]
theorem erdos_955.variants.troupe_sum_of_two_squares :
    Tendsto (fun n ↦ (count { x | ∃ a b : ℕ, s x = a^2 + b^2 } n : ℝ) / n)
      atTop (𝓝 0) := by
  sorry

/--
Pollack, Pomerance, and Thompson [PPT18] prove that if $\epsilon(x)=o(1)$ and $A\subset \mathbb{N}$
has size at most $x^{1/2+\epsilon(x)}$ then $\#\{ n\leq x: s(n)\in A\} =o(x)$ as $x\to \infty$. It
follows that (using $s(n)\ll n\log\log n$) if $A$ grows like
$\lvert A\cap [1,x]\rvert\leq x^{1/2+o(1)}$ then $s^{-1}(A)$ has density $0$.
-/
@[category research solved, AMS 11]
theorem erdos_955.variants.pollack_pomerance_thompson_bound :
    ∀ (A : Set ℕ) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n : ℕ in atTop, (count A n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε n)) →
      Tendsto (fun n ↦ (count { x | s x ∈ A } n : ℝ) / n) atTop (𝓝 0) := by
  sorry

end Erdos955
