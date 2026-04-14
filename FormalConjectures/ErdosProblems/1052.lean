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
# Erdős Problem 1052

*Reference:* [erdosproblems.com/1052](https://www.erdosproblems.com/1052)
-/

namespace Erdos1052

/-- A proper unitary divisor of $n$ is a divisor $d$ of $n$
such that $d$ is coprime to $n/d$, and $d < n$. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- A number $n > 0$ is a unitary perfect number if it is the sum of its proper unitary divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/--
Are there only finitely many unitary perfect numbers? -/
@[category research open, AMS 11]
theorem erdos_1052 :
    answer(sorry) ↔ {n | IsUnitaryPerfect n}.Finite := by
  sorry

/-- All unitary perfect numbers are even. -/
@[category research solved, AMS 11]
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  rcases ↑hn
  simp_all only[properUnitaryDivisors, (n : ℕ).even_iff]
  replace:∑ a ∈{ a ∈n.divisors | a.Coprime (n/a) },ite ( a< n) a 0=(n)
  · exact ( Finset.sum_filter _ _).symm.trans (.trans (congr_arg₂ _ (Finset.ext (by cases. with norm_num[ne_zero_of_lt (by valid), and_comm])) rfl) (‹_ = _›:))
  replace:∑ a ∈{ a ∈n.divisors | a.Coprime (n/a)} \singleton n, a =(n)
  · exact (congr_arg₂ @_ ↑( Finset.ext fun and=>by simp_all[ (and.divisor_le @_).lt_iff_ne]) rfl ).trans.comp ( Finset.sum_filter _ _).trans this
  convert n.mod_two_eq_zero_or_one.resolve_right fun and=>absurd (this▸ Finset.sum_sdiff (by norm_num[*,ne_of_gt])) (mt (congr_arg (.%2)) _)
  simp_all[←two_mul,←this▸ Finset.sum_sdiff,n.add_mod,pos_iff_ne_zero]
  replace :∑ a ∈{ a ∈n.divisors | a.Coprime (n/a) },a=n+n
  · exact (this▸ Finset.sum_sdiff (by(norm_num [@pos_iff_ne_zero ℕ, *]))).symm
  replace:∑ a ∈ n.primeFactors.powerset.image ↑(∏ a ∈ ·, a ^(n.factorization a)), a=(n)+ (n : ℕ)
  · convert←congr_arg₂ @_ (Finset.ext fun and=> _) rfl
    (aesop)
    · exact(w.prod_dvd_prod_of_subset _ _ left_1).trans (n.factorization_prod_pow_eq_self right).dvd
    · use .prod_left fun and(a)=>((((n.prime_of_mem_primeFactors ( left_1 a)).coprime_iff_not_dvd.2) (mt ((Nat.mul_dvd_of_dvd_div ((w.prod_dvd_prod_of_subset _ _ left_1).trans (n.factorization_prod_pow_eq_self right).dvd) )) ?_)).pow_left _)
      exact (Nat.pow_succ_factorization_not_dvd right (n.prime_of_mem_primeFactors ( left_1 a))).comp ((mul_dvd_mul_right.comp (w.dvd_prod_of_mem _) a _)).trans
    refine ⟨ _,and.primeFactors_mono left_1 right,.trans ( Finset.prod_congr rfl fun and β=>? _) (and.factorization_prod_pow_eq_self (ne_zero_of_dvd_ne_zero right left_1))⟩
    induction left_1 with ·norm_num[Nat.mem_primeFactors.mp β,Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd _).mp ↑( right_1.of_dvd _ _)), *, mul_ne_zero_iff.1 (by convert ←right)]
  rewrite[ Finset.sum_image] at this
  · apply absurd (congr_arg (@ ·%4) this) ∘ ↑( Finset.sum_nat_mod _ _ _).trans_ne
    have:=n.primeFactors.prod_add (·^ n.factorization (by valid) ) (1)
    rcases lt_trichotomy (n.primeFactors).card (1) with a | S | S
    · rcases Finset.card_eq_zero.1 ((Nat.lt_one_iff.mp a))▸‹_ = _+n›▸two_mul n▸(2).mul_mod_right n
    · cases Finset.card_eq_one.1 S with use absurd (n.factorization_prod_pow_eq_self) fun R=>by cases n with simp_all[Finsupp.prod]
    cases(this▸(pow_dvd_pow (2) S).trans (Finset.prod_const 2▸ Finset.prod_dvd_prod_of_dvd _ _ fun a s=>((Nat.odd_iff.2 and).of_dvd_nat (by simp_all)).pow.add_one.two_dvd)).trans ( by aesop) with omega
  use fun and R M a s=>and.ext fun M=>by_contra fun and=>absurd (congr_arg (·.factorization M) s) (and ∘? _)
  clear‹¬n=0›hn‹_=1›this s and‹_=n›
  simp_all [Nat.factorization_prod fun and x =>(pow_ne_zero _) ↑(Nat.Prime.ne_zero _), Finsupp.single_apply, Finset.subset_iff]
  exact (by repeat use fun and=>by_contra fun and' =>by simp_all[ n.factorization_eq_zero_iff,eq_comm (a :=0),·])

@[category test, AMS 11]
theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

@[category test, AMS 11]
theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

@[category test, AMS 11]
theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

@[category test, AMS 11]
theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  -- TODO: Find a quicker proof. This one is too slow.
  stop
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

@[category test, AMS 11]
theorem isUnitaryPerfect_146361946186458562560000 : IsUnitaryPerfect 146361946186458562560000 := by
  sorry

end Erdos1052
