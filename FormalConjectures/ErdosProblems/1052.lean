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

/-- All unitary divisors of `n`: `d ∣ n`, `1 ≤ d ≤ n`, and `d` is coprime to `n / d`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 (n + 1) | d ∣ n ∧ d.Coprime (n / d)}

/-- `σ*` : the sum of all unitary divisors of `n`. -/
def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- The only proper unitary divisor of a prime power `p ^ k` (with `1 ≤ k`) is `1`. -/
@[category API, AMS 11]
private lemma properUnitaryDivisors_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    properUnitaryDivisors (p ^ k) = {1} := by
  ext d
  simp only [properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, hlt⟩, hdvd, hcop⟩
    obtain ⟨j, hjk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hp1 : 1 < p := hp.one_lt
    have hjlt : j < k := (Nat.pow_lt_pow_iff_right hp1).mp hlt
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · simp [hj0]
    · exfalso
      have hdiv : p ^ k / p ^ j = p ^ (k - j) := by
        rw [Nat.pow_div hjk (by omega)]
      rw [hdiv] at hcop
      have hp_dvd_j : p ∣ p ^ j := dvd_pow_self p (by omega)
      have hp_dvd_kj : p ∣ p ^ (k - j) := dvd_pow_self p (by omega)
      have : p ∣ Nat.gcd (p ^ j) (p ^ (k - j)) := Nat.dvd_gcd hp_dvd_j hp_dvd_kj
      rw [Nat.Coprime] at hcop
      rw [hcop] at this
      have := Nat.eq_one_of_dvd_one this
      omega
  · rintro rfl
    refine ⟨⟨le_refl 1, ?_⟩, one_dvd _, ?_⟩
    · have : 1 < p := hp.one_lt
      calc 1 < p := this
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right (le_of_lt this) hk
    · simp

/-- A positive number `n` is one of its own unitary divisors. -/
@[category API, AMS 11]
private lemma self_mem_unitaryDivisors (n : ℕ) (hn : 1 ≤ n) : n ∈ unitaryDivisors n := by
  simp only [unitaryDivisors, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨hn, by omega⟩, dvd_refl n, ?_⟩
  rw [Nat.div_self hn]
  exact Nat.coprime_one_right n

/-- The proper unitary divisors of `n` are the unitary divisors with `n` removed. -/
@[category API, AMS 11]
private lemma properUnitaryDivisors_eq (n : ℕ) :
    properUnitaryDivisors n = (unitaryDivisors n).erase n := by
  ext d
  simp only [properUnitaryDivisors, unitaryDivisors, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_erase]
  constructor
  · rintro ⟨⟨h1, hlt⟩, hdvd, hcop⟩
    exact ⟨by omega, ⟨h1, by omega⟩, hdvd, hcop⟩
  · rintro ⟨hne, ⟨h1, hle⟩, hdvd, hcop⟩
    have : d < n := lt_of_le_of_ne (by omega) hne
    exact ⟨⟨h1, this⟩, hdvd, hcop⟩

/-- `n` is unitary perfect iff the sum of all its unitary divisors equals `2 * n`. -/
@[category API, AMS 11]
private lemma isUnitaryPerfect_iff_sum_unitaryDivisors (n : ℕ) :
    IsUnitaryPerfect n ↔ (∑ d ∈ unitaryDivisors n, d = 2 * n ∧ 0 < n) := by
  constructor
  · rintro ⟨hsum, hpos⟩
    refine ⟨?_, hpos⟩
    rw [properUnitaryDivisors_eq n] at hsum
    have hmem := self_mem_unitaryDivisors n hpos
    have := Finset.add_sum_erase (unitaryDivisors n) id hmem
    simp only [id] at this
    omega
  · rintro ⟨hsum, hpos⟩
    refine ⟨?_, hpos⟩
    rw [properUnitaryDivisors_eq n]
    have hmem := self_mem_unitaryDivisors n hpos
    have := Finset.add_sum_erase (unitaryDivisors n) id hmem
    simp only [id] at this
    omega

/-- `1` is not a unitary perfect number. -/
@[category API, AMS 11]
private lemma not_isUnitaryPerfect_one : ¬ IsUnitaryPerfect 1 := by
  rintro ⟨hsum, _⟩
  have : properUnitaryDivisors 1 = ∅ := by
    simp [properUnitaryDivisors]
  rw [this] at hsum
  simp at hsum

/-- No prime power `p ^ k` (with `1 ≤ k`) is unitary perfect. -/
@[category API, AMS 11]
private lemma not_unitaryPerfect_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    ¬ IsUnitaryPerfect (p ^ k) := by
  rintro ⟨hsum, _⟩
  rw [properUnitaryDivisors_prime_pow p k hp hk] at hsum
  simp only [Finset.sum_singleton] at hsum
  have hp2 : 2 ≤ p := hp.two_le
  have : 2 ≤ p ^ k := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

/-- The unitary divisors of a prime power `p ^ k` (with `1 ≤ k`) are exactly `{1, p ^ k}`. -/
@[category API, AMS 11]
private lemma unitaryDivisors_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hpos : 1 ≤ p ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hp.pos.ne')
  have hstep : unitaryDivisors (p ^ k) = insert (p ^ k) (properUnitaryDivisors (p ^ k)) := by
    rw [properUnitaryDivisors_eq]
    rw [Finset.insert_erase (self_mem_unitaryDivisors _ hpos)]
  rw [hstep, properUnitaryDivisors_prime_pow p k hp hk, Finset.pair_comm]

/-- `σ*(p ^ k) = 1 + p ^ k` for a prime power with `1 ≤ k`. -/
@[category API, AMS 11]
private lemma sigmaStar_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    sigmaStar (p ^ k) = 1 + p ^ k := by
  rw [sigmaStar, unitaryDivisors_prime_pow p k hp hk]
  rw [Finset.sum_pair]
  have hp1 : 1 < p := hp.one_lt
  have : 1 < p ^ k := by
    calc (1:ℕ) < p := hp1
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

/-- Membership criterion for the unitary divisors of a positive `n`. -/
@[category API, AMS 11]
private lemma mem_unitaryDivisors {n d : ℕ} (hn : 0 < n) :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ d.Coprime (n / d) := by
  simp only [unitaryDivisors, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨_, hdvd, hcop⟩; exact ⟨hdvd, hcop⟩
  · rintro ⟨hdvd, hcop⟩
    have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hdvd; omega)
    have hdle : d ≤ n := Nat.le_of_dvd hn hdvd
    exact ⟨⟨hdpos, by omega⟩, hdvd, hcop⟩

/-- `σ*` is multiplicative on coprime positive arguments. -/
@[category API, AMS 11]
private lemma sigmaStar_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rw [sigmaStar, sigmaStar, sigmaStar, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  -- decompose d ∣ m*n as (gcd d m)*(gcd d n) for coprime m,n
  have key : ∀ d, d ∣ m * n → d.gcd m * d.gcd n = d := by
    intro d hddvd
    have hgm : d.gcd m ∣ d := Nat.gcd_dvd_left d m
    have hgn : d.gcd n ∣ d := Nat.gcd_dvd_left d n
    have hcop_g : (d.gcd m).Coprime (d.gcd n) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right d m)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right d n) hmn)
    have hprod_dvd : d.gcd m * d.gcd n ∣ d := hcop_g.mul_dvd_of_dvd_of_dvd hgm hgn
    have hd_dvd : d ∣ d.gcd m * d.gcd n := by
      have h1 : d ∣ d.gcd m * n := dvd_gcd_mul_of_dvd_mul hddvd
      have hgm_pos : 0 < d.gcd m := Nat.gcd_pos_of_pos_right d hm
      obtain ⟨e, he⟩ := hgm  -- d = gcd(d,m) * e
      have he_dvd_n : e ∣ n := by
        have h1' : d.gcd m * e ∣ d.gcd m * n := by rw [← he]; exact h1
        exact (Nat.mul_dvd_mul_iff_left hgm_pos).mp h1'
      have he_dvd_d : e ∣ d := ⟨d.gcd m, by rw [mul_comm]; exact he⟩
      have he_gcd : e ∣ d.gcd n := Nat.dvd_gcd he_dvd_d he_dvd_n
      calc d = d.gcd m * e := he
        _ ∣ d.gcd m * d.gcd n := Nat.mul_dvd_mul_left _ he_gcd
    exact Nat.dvd_antisymm hprod_dvd hd_dvd
  apply Finset.sum_nbij' (i := fun d => (d.gcd m, d.gcd n)) (j := fun p => p.1 * p.2)
  -- hi : i maps source (unitaryDivisors (m*n)) into product
  · intro d hd
    rw [mem_unitaryDivisors (Nat.mul_pos hm hn)] at hd
    obtain ⟨hddvd, hdcop⟩ := hd
    have hgm_dvd_m : d.gcd m ∣ m := Nat.gcd_dvd_right d m
    have hgn_dvd_n : d.gcd n ∣ n := Nat.gcd_dvd_right d n
    have hgm_dvd_d : d.gcd m ∣ d := Nat.gcd_dvd_left d m
    have hgn_dvd_d : d.gcd n ∣ d := Nat.gcd_dvd_left d n
    -- decomposition of (m*n)/d
    have hkey := key d hddvd  -- d.gcd m * d.gcd n = d
    have hquot : (m * n) / d = (m / d.gcd m) * (n / d.gcd n) := by
      conv_lhs => rw [← hkey]
      rw [Nat.div_mul_div_comm hgm_dvd_m hgn_dvd_n]
    simp only [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [mem_unitaryDivisors hm]
      refine ⟨hgm_dvd_m, ?_⟩
      -- d.gcd m coprime to m / d.gcd m
      have h1 : (m / d.gcd m) ∣ (m * n) / d := by rw [hquot]; exact Dvd.intro _ rfl
      have hcop1 : d.Coprime ((m * n) / d) := hdcop
      have : d.Coprime (m / d.gcd m) := hcop1.coprime_dvd_right h1
      exact this.coprime_dvd_left hgm_dvd_d
    · rw [mem_unitaryDivisors hn]
      refine ⟨hgn_dvd_n, ?_⟩
      have h1 : (n / d.gcd n) ∣ (m * n) / d := by rw [hquot]; exact Dvd.intro_left _ rfl
      have hcop1 : d.Coprime ((m * n) / d) := hdcop
      have : d.Coprime (n / d.gcd n) := hcop1.coprime_dvd_right h1
      exact this.coprime_dvd_left hgn_dvd_d
  -- hj : j maps product into source
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    rw [mem_unitaryDivisors hm] at ha
    rw [mem_unitaryDivisors hn] at hb
    obtain ⟨hadvd, hacop⟩ := ha
    obtain ⟨hbdvd, hbcop⟩ := hb
    rw [mem_unitaryDivisors (Nat.mul_pos hm hn)]
    have hab_dvd : a * b ∣ m * n := Nat.mul_dvd_mul hadvd hbdvd
    refine ⟨hab_dvd, ?_⟩
    have hdiv : m * n / (a * b) = (m / a) * (n / b) := by
      rw [Nat.div_mul_div_comm hadvd hbdvd]
    rw [hdiv]
    have ha_n : a.Coprime n := Nat.Coprime.coprime_dvd_left hadvd hmn
    have hb_m : b.Coprime m := Nat.Coprime.coprime_dvd_left hbdvd hmn.symm
    have ha_nb : a.Coprime (n / b) := ha_n.coprime_dvd_right (Nat.div_dvd_of_dvd hbdvd)
    have hb_ma : b.Coprime (m / a) := hb_m.coprime_dvd_right (Nat.div_dvd_of_dvd hadvd)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hacop ha_nb)
      (Nat.Coprime.mul_right hb_ma hbcop)
  -- left_inv : j (i d) = d, i.e. (d.gcd m)*(d.gcd n) = d
  · intro d hd
    rw [mem_unitaryDivisors (Nat.mul_pos hm hn)] at hd
    exact key d hd.1
  -- right_inv : i (j p) = p, i.e. ((a*b).gcd m, (a*b).gcd n) = (a,b)
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    rw [mem_unitaryDivisors hm] at ha
    rw [mem_unitaryDivisors hn] at hb
    obtain ⟨hadvd, _⟩ := ha
    obtain ⟨hbdvd, _⟩ := hb
    have ha_n : a.Coprime n := Nat.Coprime.coprime_dvd_left hadvd hmn
    have hb_m : b.Coprime m := Nat.Coprime.coprime_dvd_left hbdvd hmn.symm
    have hgm : (a * b).gcd m = a := by
      rw [mul_comm a b]; exact Nat.gcd_mul_of_coprime_of_dvd hb_m hadvd
    have hgn : (a * b).gcd n = b := Nat.gcd_mul_of_coprime_of_dvd ha_n hbdvd
    rw [Prod.ext_iff]
    exact ⟨hgm, hgn⟩
  -- h : f d = g (i d), i.e. d = (d.gcd m)*(d.gcd n)
  · intro d hd
    rw [mem_unitaryDivisors (Nat.mul_pos hm hn)] at hd
    exact (key d hd.1).symm

/-- `σ*(1) = 1`. -/
@[category API, AMS 11]
private lemma sigmaStar_one : sigmaStar 1 = 1 := by
  have : unitaryDivisors 1 = {1} := by
    ext d
    simp only [unitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, _⟩; omega
    · rintro rfl; exact ⟨⟨le_refl 1, by omega⟩, dvd_refl 1, by simp⟩
  rw [sigmaStar, this, Finset.sum_singleton]

/-- `σ*` is multiplicative on coprime arguments (including the zero/one boundary cases). -/
@[category API, AMS 11]
private lemma sigmaStar_mul {m n : ℕ} (hmn : m.Coprime n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    rw [Nat.coprime_zero_left] at hmn
    subst hmn
    simp [sigmaStar_one]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [Nat.coprime_zero_right] at hmn
    subst hmn
    simp [sigmaStar_one]
  exact sigmaStar_mul_coprime hm hn hmn

/-- `σ*(n)` equals the product over the prime factorization of `n` of `1 + p ^ k`. -/
@[category API, AMS 11]
private lemma sigmaStar_eq_prod {n : ℕ} (hn : n ≠ 0) :
    sigmaStar n = n.factorization.prod fun p k => 1 + p ^ k := by
  rw [Nat.multiplicative_factorization sigmaStar (fun _ _ => sigmaStar_mul) sigmaStar_one hn]
  apply Finsupp.prod_congr
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (by
    rwa [Nat.support_factorization] at hp)
  have hk : 1 ≤ n.factorization p := by
    rw [Nat.support_factorization] at hp
    exact (Nat.Prime.factorization_pos_of_dvd hp_prime hn
      (Nat.dvd_of_mem_primeFactors hp))
  exact sigmaStar_prime_pow p _ hp_prime hk

/--
All unitary perfect numbers are even.
-/
@[category research solved, AMS 11]
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  have hpos : 0 < n := hn.2
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  -- n is odd; rule out n = 1
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have : n = 1 := by omega
    exact not_isUnitaryPerfect_one (this ▸ hn)
  -- n > 1, odd
  have hn1 : 1 < n := hge
  have hn0 : n ≠ 0 := by omega
  -- σ*(n) = 2 * n
  have hsum : sigmaStar n = 2 * n := by
    rw [sigmaStar]
    exact ((isUnitaryPerfect_iff_sum_unitaryDivisors n).mp hn).1
  -- the product formula
  have hprod := sigmaStar_eq_prod hn0
  -- every prime factor p is odd, so 1 + p^k is even
  have heven_each : ∀ p ∈ n.primeFactors, 2 ∣ (1 + p ^ (n.factorization p)) := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_odd : Odd p := by
      rcases hp_prime.eq_two_or_odd' with h2 | hodd_p
      · exfalso
        have : (2 : ℕ) ∣ n := h2 ▸ Nat.dvd_of_mem_primeFactors hp
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
      · exact hodd_p
    have : Odd (p ^ (n.factorization p)) := hp_odd.pow
    obtain ⟨j, hj⟩ := this
    rw [hj]; omega
  -- r = number of prime factors
  set r := n.primeFactors.card with hr
  have hr_pos : 1 ≤ r := by
    rw [hr]
    exact Nat.one_le_iff_ne_zero.mpr (by
      rw [Finset.card_ne_zero, Nat.nonempty_primeFactors]
      exact hn1)
  -- 2^r ∣ σ*(n)
  have hdvd_pow : 2 ^ r ∣ sigmaStar n := by
    rw [hprod]
    rw [Finsupp.prod]
    -- support of factorization = primeFactors
    have hsupp : n.factorization.support = n.primeFactors := Nat.support_factorization n
    rw [hsupp]
    calc 2 ^ r = ∏ _p ∈ n.primeFactors, 2 := by
            rw [Finset.prod_const, hr]
      _ ∣ ∏ p ∈ n.primeFactors, (1 + p ^ (n.factorization p)) :=
            Finset.prod_dvd_prod_of_dvd _ _ heven_each
  -- now derive contradiction: r must be 1, but then n is a prime power
  rw [hsum] at hdvd_pow
  -- case split on r
  rcases Nat.lt_or_ge r 2 with hr1 | hr2
  · -- r = 1 : n has exactly one prime factor, so n = p ^ (factorization p)
    have hr_eq : r = 1 := by omega
    rw [hr] at hr_eq
    -- exactly one prime factor
    obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hr_eq
    have hp_mem : p ∈ n.primeFactors := by rw [hp_eq]; exact Finset.mem_singleton_self p
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    -- n = p ^ (factorization n p)
    have hn_eq : n = p ^ (n.factorization p) := by
      conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization, hp_eq, Finset.prod_singleton]
    have hk : 1 ≤ n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp_prime hn0 (Nat.dvd_of_mem_primeFactors hp_mem)
    exact not_unitaryPerfect_prime_pow p _ hp_prime hk (hn_eq ▸ hn)
  · -- r ≥ 2 : 4 ∣ 2n, so 2 ∣ n, contradicting odd
    have h4 : (4 : ℕ) ∣ 2 * n := by
      have : (2:ℕ) ^ 2 ∣ 2 ^ r := pow_dvd_pow 2 hr2
      have : (4:ℕ) ∣ 2 ^ r := by norm_num at this ⊢; exact this
      exact this.trans hdvd_pow
    have h2n : (2 : ℕ) ∣ n := by
      obtain ⟨c, hc⟩ := h4
      refine ⟨c, ?_⟩
      omega
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2n)

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
