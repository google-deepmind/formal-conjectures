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
An odd equality with exactly four distinct prime factors is divisible by $243$.
See the [exponent exclusions and certificates](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/e9d6825f1e7aee20b1104a05a14cbefb503fd119/proofs/oeis-divisor-sums/A245212/four-prime-finiteness/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.four_prime_divisibility (n : ℕ) (hn : 1 < n) (ho : Odd n)
    (hcard : n.primeFactors.card = 4) (h : a n = (σ 1 n : ℤ)) : 243 ∣ n := by
  sorry

/--
On each prescribed finite prime support the equality set is a finite union of points
and prime-power families $mp^e$ with $e\ge 1$. See the
[effective classification](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/a5e0a2c4efbf87e21011f3a24a6991c6c1fe1ea5/proofs/oeis-divisor-sums/A245212/fixed-support/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.fixed_support_classification (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∃ F : Finset ℕ, ∃ R : Finset (ℕ × ℕ),
      (∀ mp ∈ R, mp.2 ∈ S ∧ mp.2.Prime ∧ 0 < mp.1 ∧ ¬ mp.2 ∣ mp.1) ∧
      ∀ n : ℕ, (0 < n ∧ n.primeFactors = S ∧ a n = (σ 1 n : ℤ)) ↔
        n ∈ F ∨ ∃ mp ∈ R, ∃ e : ℕ, 0 < e ∧ n = mp.1 * mp.2 ^ e := by
  sorry

/--
Among all positive $11$-smooth integers, precisely the powers of two satisfy the equality.
See the [two independent certificates](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/a5e0a2c4efbf87e21011f3a24a6991c6c1fe1ea5/proofs/oeis-divisor-sums/A245212/fixed-support).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.smooth_eleven (n : ℕ) (hn : 0 < n)
    (hsmooth : ∀ p ∈ n.primeFactors, p ≤ 11) :
    a n = (σ 1 n : ℤ) ↔ ∃ e : ℕ, n = 2 ^ e := by
  sorry

/--
Only finitely many odd positive integers with four distinct prime factors satisfy the equality.
See the [effective finiteness proof](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/e9d6825f1e7aee20b1104a05a14cbefb503fd119/proofs/oeis-divisor-sums/A245212/four-prime-finiteness/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.four_prime_finite :
    {n : ℕ | 1 < n ∧ Odd n ∧ n.primeFactors.card = 4 ∧ a n = (σ 1 n : ℤ)}.Finite := by
  sorry

/--
Every equality input $n>1$ satisfies $n<(8\omega(n))^{2\tau(n)}$.
See the [height bound](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/5d52c998277915a87728717864f5e626f4fa3b48/proofs/oeis-divisor-sums/A245212/divisor-count/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.height_bound (n : ℕ) (hn : 1 < n) (h : a n = (σ 1 n : ℤ)) :
    n < (8 * n.primeFactors.card) ^ (2 * n.divisors.card) := by
  sorry

/--
Among positive integers with at most $512$ divisors, precisely the powers of two satisfy
the equality. See the [proof and two exhaustive integer programs](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/5d52c998277915a87728717864f5e626f4fa3b48/proofs/oeis-divisor-sums/A245212/divisor-count/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.at_most_512_divisors (n : ℕ) (hn : 0 < n)
    (hcount : n.divisors.card ≤ 512) :
    a n = (σ 1 n : ℤ) ↔ ∃ e : ℕ, n = 2 ^ e := by
  sorry

/--
At each fixed number $r\ge 2$ of distinct prime factors, every odd equality input has two
distinct primary components bounded in terms of $r$.
See the [effective bound](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/3fef60dfa8ec969ced4afb1711969cdd65bf3a2f/proofs/oeis-divisor-sums/A245212/primary-components/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.two_bounded_components (r : ℕ) (hr : 2 ≤ r) :
    ∃ B : ℕ, ∀ n : ℕ, Odd n → n.primeFactors.card = r → a n = (σ 1 n : ℤ) →
      ∃ p ∈ n.primeFactors, ∃ q ∈ n.primeFactors, p ≠ q ∧
        p ^ n.factorization p ≤ B ∧ q ^ n.factorization q ≤ B := by
  sorry

/--
For an odd equality input with four distinct prime factors, some $p^e\parallel n$ satisfies
$(p-1)(e+1)<51\,204$. See the [four-prime ratio and finite certificate](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/3fef60dfa8ec969ced4afb1711969cdd65bf3a2f/proofs/oeis-divisor-sums/A245212/primary-components/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.four_prime_component_bound (n : ℕ) (ho : Odd n)
    (hcard : n.primeFactors.card = 4) (h : a n = (σ 1 n : ℤ)) :
    ∃ p ∈ n.primeFactors, (p - 1) * (n.factorization p + 1) < 51204 := by
  sorry

/--
At fixed $r\ge 2$, only finitely many odd equality inputs with $r$ distinct prime factors have
no prime exponent congruent to $2$ modulo $4$. This includes all odd fourth powers at this rank.
See the [effective finiteness proof](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/9ac47e40ce71a4f5e0b32bc57c603e2d9ca7ad30/proofs/oeis-divisor-sums/A245212/primary-components/README.md).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.finite_without_exponent_two_mod_four (r : ℕ) (hr : 2 ≤ r) :
    {n : ℕ | Odd n ∧ n.primeFactors.card = r ∧
      (∀ p ∈ n.primeFactors, n.factorization p % 4 ≠ 2) ∧ a n = (σ 1 n : ℤ)}.Finite := by
  sorry

end OeisA245212
