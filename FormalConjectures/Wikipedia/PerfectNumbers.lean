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
# Perfect numbers

A perfect number is a positive integer that equals the sum of its proper divisors
(i.e., all its positive divisors excluding the number itself).

For example, 6 is perfect because its proper divisors are 1, 2, and 3, and 1 + 2 + 3 = 6.
Similarly, 28 is perfect because 1 + 2 + 4 + 7 + 14 = 28.

All known perfect numbers are even. Several open problems about perfect numbers are
formalised here:

* Are there infinitely many perfect numbers?
* Are there infinitely many even perfect numbers?
* Do odd perfect numbers exist?

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Perfect_number)
- [Wikipedia, Odd perfect numbers](https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers)
-/

namespace PerfectNumbers

open Nat

/--
**Infinitely many perfect numbers conjecture.**
Are there infinitely many perfect numbers?

*Reference:*
[Wikipedia](https://en.wikipedia.org/wiki/Perfect_number)
-/
@[category research open, AMS 11]
theorem infinitely_many_perfect :
    answer(sorry) ↔ {n : ℕ | Perfect n}.Infinite := by
  sorry

/--
**Infinitely many even perfect numbers conjecture.**
Are there infinitely many even perfect numbers?

This is equivalent to asking whether there are infinitely many Mersenne primes,
since by the Euclid–Euler theorem an even number is perfect if and only if it
has the form $2^{p-1}(2^p - 1)$ where $2^p - 1$ is a Mersenne prime.

*Reference:*
[Wikipedia](https://en.wikipedia.org/wiki/Perfect_number)
-/
@[category research open, AMS 11]
theorem infinitely_many_even_perfect :
    answer(sorry) ↔ {n : ℕ | Perfect n ∧ Even n}.Infinite := by
  sorry

/--
**Odd Perfect Number Conjecture.**
The Odd Perfect Number Conjecture states that all perfect numbers are even.

*Reference:*
[Wikipedia](https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers)
-/
@[category research open, AMS 11]
theorem odd_perfect_number_conjecture (n : ℕ) (hn : Perfect n) : Even n := by
  sorry

/--
A known result: If an odd perfect number exists, it must be greater than $10^{1500}$
and must have at least 101 prime factors (including multiplicities).

*Reference:* Pascal Ochem, Michaël Rao (2012).
"Odd perfect numbers are greater than 10^1500"
-/
@[category research solved, AMS 11]
theorem odd_perfect_number.lower_bound (n : ℕ) (hn : Odd n) (hp : Perfect n) :
    n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101 := by
  sorry

/--
A known result: If an odd perfect number exists, it must be of the form
$p^α * m^2$ where $p$ is prime, $p \equiv 1 \pmod{4}$, $\alpha \equiv 1 \pmod{4}$,
and $p \nmid m$.

*Reference:* Euler's theorem on odd perfect numbers
-/
@[category research solved, AMS 11]
theorem odd_perfect_number.euler_form (n : ℕ) (hn : Odd n) (hp : Perfect n) :
    ∃ (p m α : ℕ),
      p.Prime ∧
      p ≡ 1 [ZMOD 4] ∧
      α ≡ 1 [ZMOD 4] ∧
      ¬ p ∣ m ∧
      n = p^α * m^2 := by
  delta Int.ModEq Nat.Perfect at*
  have:= n.sum_divisors_eq_sum_properDivisors_add_self
  rw_mod_cast [ hp.1, ← two_mul, n.sum_divisors] at this
  · by_cases h4:∃ a ∈(n).primeFactors,n.factorization a % 2 =01 ∧ (a%4)=1
    · convert h4.imp fun and x =>(Nat.odd_iff.2 x.right.left).elim fun and x =>_
      rcases and.even_or_odd with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · simp_all-contextual[n.odd_iff,<-two_mul,Finset.prod_eq_mul_prod_diff_singleton (And.left (by valid)),←mul_assoc]
        obtain ⟨c, _⟩| ⟨a, _⟩ := (∏ a ∈ n.primeFactors\{and},∑F ∈.range (n.factorization a+1), a^F).even_or_odd
        · norm_num [mul_left_cancel₀ ↑_ ↑(this.symm.trans (by rw [ (by valid:),mul_add, two_mul,])), and.pow_mod, and.odd_of_mod_four_eq_one _, *, true, Finset.sum_nat_mod, false,Nat.add_mod, true,Nat.mul_mod] at hn
        exists∏ a ∈n.primeFactors\ {and},a^(n.factorization a/2), _,x▸Nat.mul_add_mod _ _ _,?_
        · exact (‹_∧_›:).1.1.prime.not_dvd_finset_prod fun a s=>by simp_all-contextual[ne_comm, and.prime_dvd_prime_iff_eq] ∘Nat.Prime.dvd_of_dvd_pow (by push_cast[*])
        rw [← Finset.prod_pow, Finset.prod_congr rfl fun and(A) =>.trans (pow_mul _ _ _).symm ((congr_arg _) ↑(Nat.div_mul_cancel (by_contra fun and' =>absurd (congr_arg (.%2) (by valid)) ( (( Finset.prod_nat_mod _ _ _).trans_ne) ?_)))), mul_comm]
        · apply (n.factorization_prod_pow_eq_self hp.2.ne').symm.trans ( Finset.sdiff_singleton_eq_erase and @_▸ Finset.prod_erase_mul _ _ (by. (norm_num[*]))).symm
        norm_num[*, and.pow_mod, Finset.sum_nat_mod, Finset.prod_eq_zero A,Nat.add_mod,Nat.mod_two_ne_zero.1 (and'.comp (2).dvd_of_mod_eq_zero),Nat.odd_iff.1.comp (Nat.odd_iff.2 _).of_dvd_nat (by simp_all:and ∣n)]
      induction((((4)).dvd_of_mod_eq_zero (by ·norm_num[ *, mul_add, add_assoc, and.pow_mod, Finset.sum_nat_mod, false, ←mul_assoc]))).trans.comp (this▸ Finset.dvd_prod_of_mem _) ↑(‹_ ∧_›:).left with cases @hn with valid
    replace h4:∀ a ∈n.primeFactors,n.factorization a%2 = 0 :=fun A B=>(Nat.mod_two_eq_zero_or_one ↑(_)).resolve_right fun and=> absurd (congr_arg (@·%4) this) ( (( Finset.prod_nat_mod _ _ _).trans_ne) ? _)
    · simp_all[ Finset.sum_nat_mod,mt (congr_arg ( ·%2)), Finset.prod_nat_mod, false,Nat.add_mod _,Nat.odd_iff.1 ∘hn.of_dvd_nat ∘ (n : ℕ).dvd_of_mem_primeFactors,Nat.pow_mod]
    rewrite[ Finset.prod_eq_zero B]
    · induction hn with ·fin_omega
    norm_num [ (by_contra fun and' =>h4 ⟨A, B, and, (hn.of_dvd_nat (n.dvd_of_mem_primeFactors B)).elim (by valid)⟩: A%4 = 3), Finset.sum_nat_mod, A.pow_mod] at B⊢
    exact (Nat.odd_iff.mpr and).elim fun and true => true▸and.rec rfl (by norm_num[pow_add, add_assoc, mul_add,pow_mul, Finset.sum_range_succ _,Nat.add_mod,Nat.mul_mod,Nat.pow_mod])
  exact (hn).pos.ne'

end PerfectNumbers
