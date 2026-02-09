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

## Proofs

The proof of `even_of_isUnitaryPerfect` was discovered by
[Aristotle](https://aristotle.harmonic.fun) (Harmonic).
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

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

/-!
## Helpers for the evenness proof

The following section establishes the multiplicative structure of the unitary
sigma function and uses it to prove that all unitary perfect numbers are even.
-/

/-- The set of all unitary divisors of n (including 1 and n). -/
private def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- The unitary sigma function: sum of all unitary divisors. -/
private def unitarySigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- n is a unitary divisor of itself (for n ≠ 0). -/
private lemma mem_unitaryDivisors_self (n : ℕ) (hn : n ≠ 0) :
    n ∈ unitaryDivisors n := by
  simp [unitaryDivisors, hn];
  simp [Nat.div_self (Nat.pos_of_ne_zero hn)]

/-- The unitary sigma equals the sum of proper unitary divisors plus n. -/
private lemma unitarySigma_eq_sum_proper_add_self (n : ℕ) (hn : 0 < n) :
    unitarySigma n = ∑ d ∈ properUnitaryDivisors n, d + n := by
  rw [ unitarySigma ];
  rw [ show unitaryDivisors n = properUnitaryDivisors n ∪ { n } from ?_,
    Finset.sum_union ] <;> norm_num [ hn.ne' ];
  · exact fun h => by
      have := Finset.mem_Ico.mp ( Finset.mem_filter.mp h |>.1 ) ; linarith;
  · ext d; by_cases hd : d = n <;>
      simp +decide [ *, unitaryDivisors, properUnitaryDivisors ] ;
    · linarith;
    · exact ⟨ fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1.1 hn,
        lt_of_le_of_ne ( Nat.le_of_dvd hn h.1.1 ) hd ⟩, h.1.1, h.2 ⟩,
        fun h => ⟨ ⟨ h.2.1, hn.ne' ⟩, h.2.2 ⟩ ⟩

/-- n is unitary perfect iff σ*(n) = 2n. -/
private theorem isUnitaryPerfect_iff_unitarySigma_eq_two_mul (n : ℕ) (hn : 0 < n) :
    IsUnitaryPerfect n ↔ unitarySigma n = 2 * n := by
  have h_unitary_sigma :
      unitarySigma n = ∑ i ∈ properUnitaryDivisors n, i + n := by
    convert unitarySigma_eq_sum_proper_add_self n hn using 1;
  simp_all +decide [ two_mul, IsUnitaryPerfect ]

/-- σ*(n) = ∏ₚ (1 + p^{vₚ(n)}) over the prime factors of n. -/
private theorem unitarySigma_eq_prod_prime_factors (n : ℕ) (hn : n ≠ 0) :
    unitarySigma n =
      ∏ p ∈ n.primeFactors, (1 + p ^ (n.factorization p)) := by
  have h_unitary_divisors :
      ∀ d ∈ unitaryDivisors n,
        d = ∏ p ∈ n.primeFactors,
          p ^ (if p ^ (Nat.factorization n p) ∣ d
            then Nat.factorization n p else 0) := by
    intro d hd
    have h_div : d ∣ n := by
      exact Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp hd |>.1
    have h_prime_factors :
        ∀ p ∈ n.primeFactors,
          Nat.factorization d p =
            if p ^ (Nat.factorization n p) ∣ d
            then Nat.factorization n p else 0 := by
      intro p hp
      have h_div_prime :
          Nat.factorization d p ≤ Nat.factorization n p := by
        exact Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2
          h_div p;
      split_ifs <;> simp_all +decide [ Nat.factorization_eq_zero_iff ];
      · exact le_antisymm h_div_prime
          ( Nat.le_of_not_lt fun h =>
            absurd ( Nat.dvd_trans ( pow_dvd_pow _ h ) ‹_› )
              ( Nat.pow_succ_factorization_not_dvd ( by aesop ) ( by aesop ) ) );
      · contrapose! h_div_prime;
        have h_coprime : Nat.gcd d (n / d) = 1 := by
          unfold unitaryDivisors at hd; aesop;
        have h_div_prime : p ^ (Nat.factorization n p) ∣ d * (n / d) := by
          rw [ Nat.mul_div_cancel' h_div ] ; exact Nat.ordProj_dvd _ _;
        have h_div_prime : p ^ (Nat.factorization n p) ∣ d := by
          exact ( Nat.Coprime.dvd_of_dvd_mul_right
            ( show Nat.Coprime ( p ^ ( Nat.factorization n p ) ) ( n / d ) from
              Nat.Coprime.pow_left _ <|
                hp.left.coprime_iff_not_dvd.mpr fun h => by
                  have := Nat.dvd_gcd ( show p ∣ d from by tauto ) h;
                  aesop )
            h_div_prime );
        contradiction
    exact (by
    conv_lhs =>
      rw [ ← Nat.factorization_prod_pow_eq_self
        ( Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos h_div ( Nat.pos_of_ne_zero hn ) ) ) ];
    rw [ Finsupp.prod_of_support_subset ];
    exact?;
    · exact Nat.primeFactors_mono h_div hn;
    · bound);
  have h_unitary_divisors_sum :
      ∑ d ∈ unitaryDivisors n, d =
        ∑ s ∈ Finset.powerset n.primeFactors,
          (∏ p ∈ s, p ^ (Nat.factorization n p)) := by
    apply Finset.sum_bij
      (fun d hd => n.primeFactors.filter
        (fun p => p ^ (Nat.factorization n p) ∣ d)) _ _ _ <;>
      norm_num at *;
    · intro d hd; specialize h_unitary_divisors d hd;
      simp +decide [ Finset.prod_filter ] at h_unitary_divisors ⊢;
      exact h_unitary_divisors;
    · intro a₁ ha₁ a₂ ha₂ h;
      rw [ h_unitary_divisors a₁ ha₁, h_unitary_divisors a₂ ha₂ ] ;
      simp +decide [ Finset.prod_ite, h ] ;
    · intro b hb
      use ∏ p ∈ b, p ^ (Nat.factorization n p);
      refine' ⟨ _, _ ⟩;
      · refine' Finset.mem_filter.mpr ⟨ Nat.mem_divisors.mpr ⟨ _, _ ⟩, _ ⟩ <;>
          norm_num at *;
        · conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hn ];
          apply_rules [ Finset.prod_dvd_prod_of_subset ];
        · exact hn;
        · have h_coprime :
              Nat.Coprime (∏ p ∈ b, p ^ (n.factorization p))
                (∏ p ∈ n.primeFactors \ b, p ^ (n.factorization p)) := by
            apply_mod_cast Nat.Coprime.prod_right ; norm_num;
            exact fun p pp _ _ hp =>
              Nat.Coprime.prod_left fun q hq =>
                Nat.Coprime.pow_right _ <| Nat.Coprime.pow_left _ <| by
                  have := Nat.coprime_primes
                    ( Nat.prime_of_mem_primeFactors <| hb hq ) pp;
                  exact this.2 <| by rintro rfl; exact hp hq;
          convert h_coprime using 1;
          rw [ Nat.div_eq_of_eq_mul_left ];
          · exact Finset.prod_pos fun p hp =>
              pow_pos ( Nat.pos_of_mem_primeFactors ( hb hp ) ) _;
          · conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self hn ];
            rw [ mul_comm, ← Finset.prod_union ];
            · rw [ Finset.union_sdiff_of_subset hb ];
              exact?;
            · exact Finset.disjoint_sdiff;
      · ext p; simp +contextual [ Finset.subset_iff ] at *; (
        constructor <;> intro hp <;>
          simp +contextual
            [ Finset.prod_eq_prod_diff_singleton_mul <|
              show p ∈ b from ?_ ] at *; (
        contrapose! hp;
        simp +contextual
          [ Finset.prod_eq_prod_diff_singleton_mul <|
            show p ∈ n.primeFactors from ?_ ] at *; (
        intro pp dp hn;
        rw [ Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num [ pp, dp, hn ] ;
        · rw [ Nat.factorization_prod ] <;> norm_num [ pp, dp, hn ];
          · rw [ Finset.sum_eq_zero ] <;> norm_num [ pp, dp, hn ];
            · exact pos_iff_ne_zero.mpr
                ( Finsupp.mem_support_iff.mp ( by
                  exact Nat.mem_primeFactors.mpr ⟨ pp, dp, hn ⟩ ) );
            · intro x hx; specialize hb hx;
              simp +decide [ Nat.factorization_eq_zero_iff,
                hb.1.ne_one, hb.2.1, hb.2.2 ] ;
              exact Or.inr <| Or.inr <| Or.inl <| fun h => hp <| by
                have := Nat.prime_dvd_prime_iff_eq pp hb.1;
                simp_all +singlePass ;
          · exact fun x hx hx' =>
              absurd hx' ( Nat.Prime.ne_zero ( hb hx |>.1 ) );
        · exact Finset.prod_ne_zero_iff.mpr fun x hx =>
            pow_ne_zero _ ( Nat.Prime.ne_zero ( hb hx |>.1 ) )));
        exact ⟨ hb hp, Finset.dvd_prod_of_mem _ hp ⟩);
  convert h_unitary_divisors_sum using 1;
  exact?

/-- If n is odd, then 2^k divides σ*(n) where k = |primeFactors(n)|. -/
private lemma two_pow_card_primeFactors_dvd_unitarySigma (n : ℕ) (hn : Odd n)
    (hn0 : n ≠ 0) :
    2 ^ n.primeFactors.card ∣ unitarySigma n := by
  have h_unitarySigma_def :
      unitarySigma n =
        ∏ p ∈ n.primeFactors, (1 + p ^ (n.factorization p)) :=
    unitarySigma_eq_prod_prime_factors n hn0;
  convert Finset.prod_dvd_prod_of_dvd _ _ fun p hp =>
    show 2 ∣ ( 1 + p ^ ( n.factorization p ) ) from ?_ using 1;
  · norm_num;
  · simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
    exact fun h =>
      absurd ( hn.of_dvd_nat hp.2 )
        ( by simp_all +decide [ Nat.Prime.even_iff ] )

/-- If n is odd and unitary perfect, then n has at most 1 distinct prime factor. -/
private lemma card_primeFactors_le_one_of_odd_isUnitaryPerfect (n : ℕ) (hn : Odd n)
    (hup : IsUnitaryPerfect n) :
    n.primeFactors.card ≤ 1 := by
  have h_unitary_sigma : 2 * n = unitarySigma n := by
    rw [ isUnitaryPerfect_iff_unitarySigma_eq_two_mul ] at hup;
    · exact hup.symm;
    · exact Nat.pos_of_ne_zero hn.pos.ne';
  have h_unitary_sigma_def :
      unitarySigma n =
        ∏ p ∈ n.primeFactors, (1 + p ^ (n.factorization p)) := by
    convert unitarySigma_eq_prod_prime_factors n _ using 1;
    aesop_cat;
  have h_div : 2 ^ (n.primeFactors).card ∣ 2 * n := by
    have h_div :
        ∀ p ∈ n.primeFactors, 2 ∣ (1 + p ^ (n.factorization p)) := by
      simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
      exact fun p pp dp _ hp =>
        absurd ( pp.even_iff.mp hp )
          ( by rintro rfl; exact absurd ( hn.of_dvd_nat dp ) ( by decide ) );
    exact h_unitary_sigma.symm ▸ h_unitary_sigma_def.symm ▸
      dvd_trans ( by simpa )
        ( Finset.prod_dvd_prod_of_dvd _ _ h_div );
  have h_card_le_one : 2 ^ (n.primeFactors).card ∣ 2 := by
    exact Nat.Coprime.dvd_of_dvd_mul_right
      ( Nat.Coprime.pow_left _ <| by
        obtain ⟨ k, rfl ⟩ := hn; norm_num ) h_div;
  exact le_of_not_gt fun h =>
    absurd ( dvd_trans ( pow_dvd_pow _ h ) h_card_le_one ) ( by norm_num )

/-- All unitary perfect numbers are even. -/
@[category research solved, AMS 11]
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) :
    Even n := by
  by_contra h_odd_n
  have h_card_prime_factors : n.primeFactors.card ≤ 1 := by
    apply card_primeFactors_le_one_of_odd_isUnitaryPerfect n (by
    grind) hn
  have h_n_form : ∃ p k, n = p ^ k ∧ p.Prime := by
    interval_cases _ : n.primeFactors.card <;>
      simp_all +decide [ Finset.card_eq_one ];
    · cases ‹_› <;> simp_all +decide [ IsUnitaryPerfect ];
    · rcases ‹∃ a, n.primeFactors = { a }› with ⟨ p, hp ⟩ ;
      rw [ ← Nat.factorization_prod_pow_eq_self ( by aesop_cat : n ≠ 0 ) ] ;
      exact ⟨ p, ⟨ n.factorization p, by
        rw [ Finsupp.prod ] ; aesop_cat ⟩,
        Nat.prime_of_mem_primeFactors <|
          hp.symm ▸ Finset.mem_singleton_self _ ⟩ ;
  obtain ⟨p, k, hn_eq, hp_prime⟩ := h_n_form
  have h_unitary_sigma : unitarySigma n = 1 + n := by
    rcases k with ( _ | k ) <;>
      simp_all +decide [ Nat.primeFactors_pow ];
    · cases hn ; contradiction;
    · convert unitarySigma_eq_prod_prime_factors ( p ^ ( k + 1 ) )
        ( pow_ne_zero _ hp_prime.ne_zero ) using 1 ;
      simp +decide [ hp_prime.ne_zero, hp_prime.ne_one,
        Nat.primeFactors_pow ] ; ring;
      simp +decide [ hp_prime.factorization, pow_succ', mul_assoc,
        mul_comm, mul_left_comm, Finset.prod_singleton ] ; ring;
      simp +decide [ hp_prime.primeFactors, Finsupp.single_apply ] ; ring;
  have h_contradiction : 1 + n = 2 * n := by
    rw [ ← h_unitary_sigma,
      isUnitaryPerfect_iff_unitarySigma_eq_two_mul n
        ( Nat.pos_of_ne_zero ( by aesop ) ) |>.1 hn ]
  have h_n_one : n = 1 := by
    grind
  exact absurd h_n_one (by
  exact ne_of_gt ( lt_of_le_of_ne hn.2
    ( Ne.symm <| by
      rintro rfl;
      exact absurd hn.1 <| by native_decide ) ))

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
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

@[category test, AMS 11]
theorem isUnitaryPerfect_146361946186458562560000 : IsUnitaryPerfect 146361946186458562560000 := by
  sorry

end Erdos1052
