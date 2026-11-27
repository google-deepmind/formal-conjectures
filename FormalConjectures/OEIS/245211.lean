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
# Sum of $d \cdot \tau(d)$ over proper divisors $d$ of $n$

The sequence $a(n)$ is the sum of $d \cdot \tau(d)$ over all proper divisors $d < n$ of $n$,
where $\tau(d)$ is the number of divisors of $d$:
$$a(n) = \sum_{d \mid n, d < n} d \cdot \tau(d)$$

*References:*
- [A245211](https://oeis.org/A245211)
-/

@[expose] public section

namespace OeisA245211

open Finset

/-- Sum over all proper divisors $d$ of $n$ of $d \cdot \tau(d)$, where $\tau(d)$ is the
number of divisors of $d$. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d * d.divisors.card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide

/--
Conjecture: $21$ is the only positive integer $n$ such that $a(n) = n$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : a n = n ↔ n = 21 := by
  sorry

/--
If a positive integer $n$ has a prime divisor at most 257, then $a(n) = n$ exactly when
$n = 21$. Two independent exhaustive programs verify the finite cases in the
[computer-assisted proof](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/4e6809caad9a8a72b72182dea47ddcc4bce87596/proofs/oeis-divisor-sums/A245211/least-prime-257).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.small_prime_factor (n : ℕ) (hn : 0 < n)
    (hp : ∃ p ∈ n.primeFactors, p ≤ 257) : a n = n ↔ n = 21 := by
  sorry

/--
For $X \geq 10^{100}$, the proportion of fixed points among the positive integers up to
$X$ is less than one in $120\,000\,000$. See the [quantitative bound](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/0d4f34b5e72421de27457f886fbdd8ef018870d0/proofs/oeis-divisor-sums/A245212/A245212-Density-Zero.pdf).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.quantitative_sparsity (X : ℕ) (hX : 10 ^ 100 ≤ X) :
    120000000 * ((Finset.Icc 1 X).filter (fun n => a n = n)).card < X := by
  sorry

end OeisA245211
