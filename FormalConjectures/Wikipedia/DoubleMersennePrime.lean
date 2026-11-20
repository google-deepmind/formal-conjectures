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
# Double Mersenne Primes

Given a prime $p$, write $M_{M_p} = 2^{2^p - 1} - 1$ for the iterated Mersenne value at $p$.
Exponents $p \in \{2, 3, 5, 7\}$ yield primes ($7$, $127$, $2^{31} - 1$, and $2^{127} - 1$), while
explicit prime divisors are known for $p \in \{13, 17, 19, 31\}$. Heuristics due to Good (1955)
suggest that no further primes occur in this family.

*References:*
- [Wikipedia: Double Mersenne number](https://en.wikipedia.org/wiki/Double_Mersenne_number)
- [OEIS A077586](https://oeis.org/A077586)
- I. J. Good, *Conjectures concerning the Mersenne numbers*, Math. Tables Aids Comput. **9**
  (1955), 120–121.
-/

@[expose] public section

namespace DoubleMersennePrime

/-- Iterated Mersenne value $M_{M_n} = 2^{2^n - 1} - 1$, defined via Mathlib's `mersenne`. -/
def doubleMersenne (n : ℕ) : ℕ :=
  mersenne (mersenne n)

/-- Primality of $M_{M_n}$ forces both $M_n$ and $n$ to be prime. -/
@[category API, AMS 11]
theorem doubleMersenne_prime_imp_exponents_prime {n : ℕ} (h : (doubleMersenne n).Prime) :
    (mersenne n).Prime ∧ n.Prime := by
  have hm : (mersenne n).Prime := h.of_mersenne
  exact ⟨hm, hm.of_mersenne⟩

/-- Exponents $p = 2$ and $p = 3$ yield primes $7$ and $127$. -/
@[category test, AMS 11]
theorem doubleMersenne_prime_two_and_three :
    (doubleMersenne 2).Prime ∧ (doubleMersenne 3).Prime := by
  unfold doubleMersenne mersenne
  decide

/-- Inputs $n = 0, 1, 4$ give $0$, $1$, and $2^{15} - 1 = 32767$, all non-prime. -/
@[category test, AMS 11]
theorem not_doubleMersenne_prime_zero_one_four :
    ¬ (doubleMersenne 0).Prime ∧ ¬ (doubleMersenne 1).Prime ∧ ¬ (doubleMersenne 4).Prime := by
  unfold doubleMersenne mersenne
  norm_num

/--
No fifth iterated Mersenne value $M_{M_p} = 2^{2^p - 1} - 1$ is prime beyond $p = 7$.
-/
@[category research open, AMS 11]
theorem no_fifth_double_mersenne_prime :
    ¬ ∃ p : ℕ, 7 < p ∧ (doubleMersenne p).Prime := by
  sorry

/--
Only finitely many exponents $p$ make $M_{M_p} = 2^{2^p - 1} - 1$ prime.
-/
@[category research open, AMS 11]
theorem no_fifth_double_mersenne_prime.variants.finite :
    {p : ℕ | (doubleMersenne p).Prime}.Finite := by
  sorry

end DoubleMersennePrime
