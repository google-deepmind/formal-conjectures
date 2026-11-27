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
# Difference between $n \tau(n)$ and $\sum_{d \mid n, d < n} d \tau(d)$

The sequence $a(n) = n \tau(n) - \sum_{d \mid n, d < n} d \tau(d)$, where $\tau(n)$ is the number
of divisors of $n$.

*References:*
- [A245212](https://oeis.org/A245212)
-/

@[expose] public section

namespace OeisA245212

open Nat Finset
open scoped ArithmeticFunction.sigma

/-- $a(n) = n \tau(n) - \sum_{d \mid n, d < n} d \tau(d)$, where $\tau(n)$
is the number of divisors of $n$. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * (n.divisors.card : ℤ) - ∑ d ∈ n.properDivisors, (d : ℤ) * (d.divisors.card : ℤ)

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by rfl

/-- Conjecture: $a(n) = \sigma(n)$ iff $n$ is a power of $2$ (A000079). -/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (h : 0 < n) :
    a n = (σ 1 n : ℤ) ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The positive integers $n$ for which $a(n) = \sigma(n)$ have natural density zero. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/open-math-agents/blob/077fa5a8106ea2fe4cbb16236ca655e9edb353b7/reductions/OeisA245212.conjecture.R1.H2.R1.lean#L466"]
theorem conjecture.variants.density_zero :
    Filter.Tendsto (fun X : ℕ =>
      (((Icc 1 X).filter (fun n => a n = (σ 1 n : ℤ))).card : ℝ) / X)
      Filter.atTop (nhds 0) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
If $n$ has at least two distinct prime factors, then
$\varphi(n)(a(n)-\sigma(n)) \geq n(2\varphi(n)-n)(\tau(n)-1)$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/open-math-agents/blob/ef13d3fa91ba444a4a5843fbad96bb5f3731f7f5/proofs/OeisA245212.conjecture.R1.H1.R1.H1.lean#L162"]
theorem conjecture.variants.totient_gap (n : ℕ) (hn : 1 < n) (h : 1 < n.primeFactors.card) :
    (n : ℤ) * (2 * (n.totient : ℤ) - n) * ((n.divisors.card : ℤ) - 1) ≤
      (n.totient : ℤ) * (a n - (σ 1 n : ℤ)) := by
  sorry

/--
For $X \geq 10^{100}$, the proportion of solutions of $a(n) = \sigma(n)$ among the positive integers up to
$X$ is less than one in $120\,000\,000$. See the [quantitative bound](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/0d4f34b5e72421de27457f886fbdd8ef018870d0/proofs/oeis-divisor-sums/A245212/A245212-Density-Zero.pdf).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.quantitative_sparsity (X : ℕ) (hX : 10 ^ 100 ≤ X) :
    120000000 * ((Finset.Icc 1 X).filter (fun n => a n = (σ 1 n : ℤ))).card < X := by
  sorry

/--
There are no solutions with exactly one distinct odd prime factor.
See the [odd-part proof](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/0d4f34b5e72421de27457f886fbdd8ef018870d0/proofs/oeis-divisor-sums/A245212/A245212-Prime-Powers-and-Density.pdf).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.one_odd_prime (p e k : ℕ) (hp : p.Prime) (ho : Odd p) (he : 0 < e) :
    a (2 ^ k * p ^ e) ≠ (σ 1 (2 ^ k * p ^ e) : ℤ) := by
  sorry

/--
For each odd part $m > 1$, at most one exponent $k$ gives a solution $2^k m$.
See the [odd-part proof](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/0d4f34b5e72421de27457f886fbdd8ef018870d0/proofs/oeis-divisor-sums/A245212/A245212-Prime-Powers-and-Density.pdf).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.unique_two_exponent (m k l : ℕ) (hm : 1 < m) (ho : Odd m)
    (hk : a (2 ^ k * m) = (σ 1 (2 ^ k * m) : ℤ))
    (hl : a (2 ^ l * m) = (σ 1 (2 ^ l * m) : ℤ)) : k = l := by
  sorry

/--
An odd counterexample has at least four distinct prime factors and exceeds twice its totient.
See the [three-prime proof and certificates](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/0d4f34b5e72421de27457f886fbdd8ef018870d0/proofs/oeis-divisor-sums/A245212/odd-three-primes/A245212-Odd-Three-Prime-Certificate.pdf).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.odd_counterexample (n : ℕ) (hn : 1 < n) (ho : Odd n)
    (h : a n = (σ 1 n : ℤ)) : 4 ≤ n.primeFactors.card ∧ 2 * n.totient < n := by
  sorry

/--
The positive integers on which $a(n)$ and $\sigma(n)$ have opposite parities have natural density
$\pi^2/12$. See the [Euler-product proof](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/0d4f34b5e72421de27457f886fbdd8ef018870d0/proofs/oeis-divisor-sums/A245212/A245212-Prime-Powers-and-Density.pdf).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.parity_mismatch_density :
    Filter.Tendsto (fun X : ℕ =>
      (((Icc 1 X).filter (fun n => Odd (a n - (σ 1 n : ℤ)))).card : ℝ) / X)
      Filter.atTop (nhds (Real.pi ^ 2 / 12)) := by
  sorry

/--
For an odd integer $n=p^e q^f$ with distinct prime divisors,
$8(a(n)-\sigma(n))\ge n\tau(n)$. See the
[two-prime proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.two_prime_gap (p q e f : ℕ) (hp : p.Prime) (hq : q.Prime)
    (ho : Odd p) (hpq : p < q) (he : 0 < e) (hf : 0 < f) :
    let n := p ^ e * q ^ f
    (n : ℤ) * n.divisors.card ≤ 8 * (a n - (σ 1 n : ℤ)) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For $n=3p^e q^f r^g$ with $3<p<q<r$ prime and positive exponents,
$288(a(n)-\sigma(n))\geq37n\tau(n)$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/ProofPlaygrond/blob/84749edd14fabb9135d6bbf8fa23c54a6f454571/proofs/oeis-divisor-sums/A245212/four-primes/FourPrimes.lean"]
theorem conjecture.variants.four_prime_gap (p q r e f g : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hp5 : 5 ≤ p) (hpq : p < q) (hqr : q < r)
    (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    let n := 3 * p ^ e * q ^ f * r ^ g
    37 * (n : ℤ) * n.divisors.card ≤ 288 * (a n - (σ 1 n : ℤ)) := by
  sorry

/--
An odd equality with exactly four distinct prime factors is divisible by $27$.
See the [proof and two exact certificates](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/9644e2a2d2d46353a6531f88f3d67bdc4f65fd50/proofs/oeis-divisor-sums/A245212/three-squared).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.four_prime_divisibility (n : ℕ) (hn : 1 < n) (ho : Odd n)
    (hcard : n.primeFactors.card = 4) (h : a n = (σ 1 n : ℤ)) : 27 ∣ n := by
  sorry

end OeisA245212
