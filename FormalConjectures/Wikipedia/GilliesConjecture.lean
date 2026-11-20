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
module

public import FormalConjecturesUtil

/-!
# Gillies' Conjecture on Mersenne Prime Counts

Donald B. Gillies (1964) proposed a Poisson model governing prime factors of $M_p = 2^p - 1$.
It implies that the count of Mersenne primes below $x$ grows asymptotically like
$(2 \log \log x) / \log 2$ as $x \to \infty$, or equivalently $(2 / \log 2) \log n$ for exponents
$p \le n$—conflicting with the Lenstra–Pomerance–Wagstaff constant $e^\gamma / \log 2$.

*References:*
- [Wikipedia: Gillies' conjecture](https://en.wikipedia.org/wiki/Gillies%27_conjecture)
- D. B. Gillies, *Three new Mersenne primes and a statistical theory*, Math. Comp. **18** (1964),
  93–97.
-/

@[expose] public section

open Asymptotics Filter

namespace GilliesConjecture

/-- Count of Mersenne primes $M_p = 2^p - 1$ strictly below $x$. -/
noncomputable def mersennePrimesBelow (x : ℝ) : ℕ :=
  {q : ℕ | q.Prime ∧ (q : ℝ) < x ∧ ∃ p : ℕ, mersenne p = q}.ncard

/-- Count of exponents $p \le n$ for which $M_p = 2^p - 1$ is prime. -/
def mersennePrimeExponentCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun p => (mersenne p).Prime).card

/--
Mersenne-prime counting consequence of Gillies' 1964 conjecture: the count of Mersenne primes
strictly below $x$ is asymptotic to $\frac{2 \log \log x}{\log 2}$ as $x \to \infty$.
-/
@[category research open, AMS 11]
theorem gillies_mersenne_prime_asymptotic :
    (fun x : ℝ => (mersennePrimesBelow x : ℝ)) ~[atTop]
      (fun x : ℝ => 2 * Real.log (Real.log x) / Real.log 2) := by
  sorry

/--
Equivalent exponent-counting formulation: the count of exponents $p \le n$ with $M_p$ prime is
asymptotic to $(2 / \log 2) \log n$ as $n \to \infty$.
-/
@[category research open, AMS 11]
theorem gillies_mersenne_prime_asymptotic.variants.exponent_count :
    (fun n : ℕ => (mersennePrimeExponentCount n : ℝ)) ~[atTop]
      (fun n : ℕ => (2 / Real.log 2) * Real.log (n : ℝ)) := by
  sorry

/-- For $n = 4$, only $p = 2, 3$ ($M_2 = 3, M_3 = 7$) give primes. -/
@[category test, AMS 11]
theorem mersennePrimeExponentCount_four :
    mersennePrimeExponentCount 4 = 2 := by
  decide

/-- Up to $n = 7$, the prime-yielding exponents are $2, 3, 5, 7$, giving count $4$. -/
@[category test, AMS 11]
theorem mersennePrimeExponentCount_seven :
    mersennePrimeExponentCount 7 = 4 := by
  decide

end GilliesConjecture
