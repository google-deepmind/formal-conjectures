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
# Erdős Problem 1074

*Reference:* [erdosproblems.com/1074](https://www.erdosproblems.com/1074)
-/

open scoped Nat

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
abbrev Nat.EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes $p$ such that there exists an $m \ge 1$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$-/
abbrev Nat.PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m ≥ 1, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

@[category test, AMS 11]
theorem test : ¬ 2 ∈ Nat.PillaiPrimes := by
  norm_num
  intro m hm h
  exact (Nat.dvd_factorial (by decide) (hm.lt_of_ne (by bound))).modEq_zero_nat.add_right 1

@[category test, AMS 11]
theorem test' : 23 ∈ Nat.PillaiPrimes := by
  norm_num
  use 14
  decide

namespace Erdos1074

open Nat

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. Does
$$
  \lim\frac{|S\cap[1, x]|}{x}
$$
exist? -/
@[category research open, AMS 11]
theorem erdos_1074.parts.i : answer(sorry) ↔ ∃ c, EHSNumbers.HasDensity c := by
  sorry

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. What is
$$
  \lim\frac{|S\cap[1, x]|}{x}?
$$ -/
@[category research open, AMS 11]
theorem erdos_1074.parts.ii : EHSNumbers.HasDensity answer(sorry) := by
  sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then does
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}
$$
exist? -/
@[category research open, AMS 11]
theorem erdos_1074.parts.iii : answer(sorry) ↔ ∃ c, PillaiPrimes.HasDensity c {p | p.Prime} := by
  sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then what is
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}?
$$ -/
@[category research open, AMS 11]
theorem erdos_1074.parts.iv :
    PillaiPrimes.HasDensity answer(sorry) {p | p.Prime} := by
  sorry

/-- Pillai [Pi30] raised the question of whether there exist any primes in $P$. This was answered
by Chowla, who noted that, for example, $14! + 1 \equiv 18! + 1 \equiv 0 \pmod{23}$. -/
@[category test, AMS 11]
theorem erdos_1074.variants.mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  norm_num
  exact ⟨14, by decide⟩

/-- Erdős, Hardy, and Subbarao proved that $S$ is infinite. -/
@[category research formally solved using formal_conjectures at
    "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1074.lean", AMS 11]
theorem erdos_1074.variants.EHSNumbers_infinite : EHSNumbers.Infinite := by
  sorry

/-- Erdős, Hardy, and Subbarao proved that $P$ is infinite. -/
@[category research formally solved using formal_conjectures at
    "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1074.lean", AMS 11]
theorem erdos_1074.variants.PillaiPrimes_infinite : PillaiPrimes.Infinite := by
  sorry

noncomputable instance : DecidablePred EHSNumbers := Classical.decPred _
noncomputable instance : DecidablePred PillaiPrimes := Classical.decPred _

/-- Kernel-reducible primality test: p is prime iff p ≥ 2 and no k in [2..p-1] divides p. -/
private def isPrimeK (p : ℕ) : Bool :=
  (2 ≤ p) && (List.range (p - 2)).all (fun k => p % (k + 2) != 0)

/-- Compute `m! mod p` iteratively to avoid materializing large factorials. -/
private def factMod (m p : ℕ) : ℕ :=
  (List.range m).foldl (fun acc k => acc * (k + 1) % p) 1

private lemma isPrimeK_iff (p : ℕ) : isPrimeK p = true ↔ p.Prime := by
  simp only [isPrimeK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, Nat.prime_def_lt']
  constructor
  · intro ⟨h2, hall⟩
    refine ⟨h2, fun m hm2 hmp hmdvd => ?_⟩
    have hk : m - 2 < p - 2 := by omega
    have hmk := hall (m - 2) hk
    have hm2eq : m - 2 + 2 = m := by omega
    rw [hm2eq] at hmk
    exact hmk (Nat.mod_eq_zero_of_dvd hmdvd)
  · intro ⟨h2, hall⟩
    refine ⟨h2, fun k hk => ?_⟩
    have hk2 : k + 2 < p := by omega
    intro hmod
    exact hall (k + 2) (by omega) hk2 (Nat.dvd_of_mod_eq_zero hmod)

private lemma factMod_succ (n p : ℕ) : factMod (n + 1) p = factMod n p * (n + 1) % p := by
  simp [factMod, List.range_succ, List.foldl_append]

private lemma factMod_spec (m p : ℕ) (hp : 1 < p) : factMod m p = m ! % p := by
  induction m with
  | zero => simp [factMod, Nat.factorial, Nat.mod_eq_of_lt hp]
  | succ n ih =>
    rw [factMod_succ, ih, Nat.factorial_succ, Nat.mul_comm (n + 1) n !]
    rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl p), ← Nat.mul_mod]

private lemma factMod_zero_mod (m p : ℕ) (hp : 1 < p) :
    (factMod m p + 1) % p = (m ! + 1) % p := by
  rw [factMod_spec m p hp]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl p), ← Nat.add_mod]

private lemma pillai_m_lt_p {p m : ℕ} (hp : p.Prime) (hm : p ∣ m ! + 1) : m < p := by
  by_contra! h
  have h1 : p ∣ m ! := dvd_factorial hp.pos h
  have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hm
  exact hp.not_dvd_one h2

private def isPillaiPrime (p : ℕ) : Bool :=
  isPrimeK p &&
  (List.range p).any (fun m =>
    (1 ≤ m) && ((p - 1) % m != 0) && ((factMod m p + 1) % p == 0))

private def checkEHS (m p : ℕ) : Bool :=
  isPrimeK p && (p % m != 1 % m) && ((factMod m p + 1) % p == 0)

private lemma isPillaiPrime_iff (p : ℕ) : p ∈ PillaiPrimes ↔ isPillaiPrime p = true := by
  dsimp [PillaiPrimes, isPillaiPrime]
  rw [Bool.and_eq_true, List.any_eq_true]
  rw [← isPrimeK_iff]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hpK, ⟨m, hm1, hm2, hm3⟩⟩
    have hp : p.Prime := (isPrimeK_iff p).mp hpK
    have h_lt : m < p := pillai_m_lt_p hp hm3
    refine ⟨hpK, ⟨m, h_lt, ⟨hm1, ?_⟩, ?_⟩⟩
    · intro h_mod
      apply hm2
      have hp1 : 1 ≤ p := hp.one_le
      have hdvd : m ∣ p - 1 := Nat.dvd_of_mod_eq_zero h_mod
      exact ((Nat.modEq_iff_dvd' hp1).mpr hdvd).symm
    · rw [Nat.dvd_iff_mod_eq_zero] at hm3
      have : (factMod m p + 1) % p = (m ! + 1) % p := factMod_zero_mod m p hp.two_le
      rw [this]; exact hm3
  · rintro ⟨hpK, m, hm_in, ⟨hm1, hm2⟩, hm3⟩
    have hp : p.Prime := (isPrimeK_iff p).mp hpK
    refine ⟨hpK, m, hm1, ?_, ?_⟩
    · intro h_mod
      apply hm2
      have hp1 : 1 ≤ p := hp.one_le
      have hdvd : m ∣ p - 1 := (Nat.modEq_iff_dvd' hp1).mp h_mod.symm
      exact Nat.mod_eq_zero_of_dvd hdvd
    · rw [Nat.dvd_iff_mod_eq_zero]
      have : (factMod m p + 1) % p = (m ! + 1) % p := factMod_zero_mod m p hp.two_le
      rw [← this]; exact hm3

private lemma checkEHS_eq {m p : ℕ} :
    checkEHS m p = true ↔ p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1 := by
  dsimp [checkEHS]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hpK, hmod⟩, hdvd_mod⟩
    have hp : p.Prime := (isPrimeK_iff p).mp hpK
    refine ⟨hp, ?_, ?_⟩
    · intro h_eq; exact hmod h_eq
    · rw [Nat.dvd_iff_mod_eq_zero]
      have heq : (factMod m p + 1) % p = (m ! + 1) % p := factMod_zero_mod m p hp.two_le
      rw [← heq]; exact hdvd_mod
  · rintro ⟨hp, hmod, hdvd⟩
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    refine ⟨⟨(isPrimeK_iff p).mpr hp, ?_⟩, ?_⟩
    · intro h_eq; exact hmod h_eq
    · have heq : (factMod m p + 1) % p = (m ! + 1) % p := factMod_zero_mod m p hp.two_le
      rw [heq]; exact hdvd

private lemma count_pillai (n : ℕ) :
    count PillaiPrimes n = (List.range n).countP (fun p => isPillaiPrime p) := by
  classical
  rw [count]
  apply List.countP_congr
  intro a _
  simp only [decide_eq_true_eq]
  exact isPillaiPrime_iff a

private lemma pillai_23 : 23 ∈ PillaiPrimes := by rw [isPillaiPrime_iff]; decide
private lemma c_23 : count PillaiPrimes 23 = 0 := by rw [count_pillai]; decide
private lemma nth_pillai_0 : nth PillaiPrimes 0 = 23 := by
  classical
  have := @nth_count PillaiPrimes _ 23 pillai_23
  rwa [c_23] at this

private lemma pillai_29 : 29 ∈ PillaiPrimes := by rw [isPillaiPrime_iff]; decide
private lemma c_29 : count PillaiPrimes 29 = 1 := by rw [count_pillai]; decide
private lemma nth_pillai_1 : nth PillaiPrimes 1 = 29 := by
  classical
  have := @nth_count PillaiPrimes _ 29 pillai_29
  rwa [c_29] at this

private lemma pillai_59 : 59 ∈ PillaiPrimes := by rw [isPillaiPrime_iff]; decide
private lemma c_59 : count PillaiPrimes 59 = 2 := by rw [count_pillai]; decide
private lemma nth_pillai_2 : nth PillaiPrimes 2 = 59 := by
  classical
  have := @nth_count PillaiPrimes _ 59 pillai_59
  rwa [c_59] at this

private lemma pillai_61 : 61 ∈ PillaiPrimes := by rw [isPillaiPrime_iff]; decide
private lemma c_61 : count PillaiPrimes 61 = 3 := by rw [count_pillai]; decide
private lemma nth_pillai_3 : nth PillaiPrimes 3 = 61 := by
  classical
  have := @nth_count PillaiPrimes _ 61 pillai_61
  rwa [c_61] at this

private lemma pillai_67 : 67 ∈ PillaiPrimes := by rw [isPillaiPrime_iff]; decide
private lemma c_67 : count PillaiPrimes 67 = 4 := by rw [count_pillai]; decide
private lemma nth_pillai_4 : nth PillaiPrimes 4 = 67 := by
  classical
  have := @nth_count PillaiPrimes _ 67 pillai_67
  rwa [c_67] at this

private lemma pillai_71 : 71 ∈ PillaiPrimes := by rw [isPillaiPrime_iff]; decide
private lemma c_71 : count PillaiPrimes 71 = 5 := by rw [count_pillai]; decide
private lemma nth_pillai_5 : nth PillaiPrimes 5 = 71 := by
  classical
  have := @nth_count PillaiPrimes _ 71 pillai_71
  rwa [c_71] at this

private lemma not_ehs_0 : 0 ∉ EHSNumbers := by intro h; cases h.1

private lemma not_ehs_1 : 1 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 1 ! + 1 = 2 := by decide
  rw [h_fact] at hdvd
  have hp2 : Nat.Prime 2 := by norm_num
  have : p = 2 := (hp2.eq_one_or_self_of_dvd p hdvd).resolve_left hp.ne_one
  subst this; revert hmod; decide

private lemma not_ehs_2 : 2 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 2 ! + 1 = 3 := by decide
  rw [h_fact] at hdvd
  have hp3 : Nat.Prime 3 := by norm_num
  have : p = 3 := (hp3.eq_one_or_self_of_dvd p hdvd).resolve_left hp.ne_one
  subst this; revert hmod; decide

private lemma not_ehs_3 : 3 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 3 ! + 1 = 7 := by decide
  rw [h_fact] at hdvd
  have hp7 : Nat.Prime 7 := by norm_num
  have : p = 7 := (hp7.eq_one_or_self_of_dvd p hdvd).resolve_left hp.ne_one
  subst this; revert hmod; decide

private lemma not_ehs_4 : 4 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 4 ! + 1 = 5 * 5 := by decide
  rw [h_fact] at hdvd
  have hp5 : Nat.Prime 5 := by norm_num
  rcases hp.dvd_mul.mp hdvd with h5 | h5
  · have : p = 5 := (hp5.eq_one_or_self_of_dvd p h5).resolve_left hp.ne_one
    subst this; revert hmod; decide
  · have : p = 5 := (hp5.eq_one_or_self_of_dvd p h5).resolve_left hp.ne_one
    subst this; revert hmod; decide

private lemma not_ehs_5 : 5 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 5 ! + 1 = 11 * 11 := by decide
  rw [h_fact] at hdvd
  have hp11 : Nat.Prime 11 := by norm_num
  rcases hp.dvd_mul.mp hdvd with h11 | h11
  · have : p = 11 := (hp11.eq_one_or_self_of_dvd p h11).resolve_left hp.ne_one
    subst this; revert hmod; decide
  · have : p = 11 := (hp11.eq_one_or_self_of_dvd p h11).resolve_left hp.ne_one
    subst this; revert hmod; decide

private lemma not_ehs_6 : 6 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 6 ! + 1 = 7 * 103 := by decide
  rw [h_fact] at hdvd
  have hp7 : Nat.Prime 7 := by norm_num
  have hp103 : Nat.Prime 103 := by norm_num
  rcases hp.dvd_mul.mp hdvd with h7 | h103
  · have : p = 7 := (hp7.eq_one_or_self_of_dvd p h7).resolve_left hp.ne_one
    subst this; revert hmod; decide
  · have : p = 103 := (hp103.eq_one_or_self_of_dvd p h103).resolve_left hp.ne_one
    subst this; revert hmod; decide

private lemma not_ehs_7 : 7 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 7 ! + 1 = 71 * 71 := by decide
  rw [h_fact] at hdvd
  have hp71 : Nat.Prime 71 := by norm_num
  rcases hp.dvd_mul.mp hdvd with h71 | h71
  · have : p = 71 := (hp71.eq_one_or_self_of_dvd p h71).resolve_left hp.ne_one
    subst this; revert hmod; decide
  · have : p = 71 := (hp71.eq_one_or_self_of_dvd p h71).resolve_left hp.ne_one
    subst this; revert hmod; decide

private lemma not_ehs_10 : 10 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 10 ! + 1 = 11 * 329891 := by decide
  rw [h_fact] at hdvd
  have hp11 : Nat.Prime 11 := by norm_num
  have hp329 : Nat.Prime 329891 := by norm_num
  rcases (hp.dvd_mul.mp hdvd) with hdvd11 | hdvd329
  · have : p = 11 := (hp11.eq_one_or_self_of_dvd p hdvd11).resolve_left hp.ne_one
    subst this; revert hmod; decide
  · have : p = 329891 := (hp329.eq_one_or_self_of_dvd p hdvd329).resolve_left hp.ne_one
    subst this; revert hmod; decide

private lemma not_ehs_11 : 11 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 11 ! + 1 = 39916801 := by decide
  rw [h_fact] at hdvd
  have hp39 : Nat.Prime 39916801 := by norm_num
  have : p = 39916801 := (hp39.eq_one_or_self_of_dvd p hdvd).resolve_left hp.ne_one
  subst this; revert hmod; decide

private lemma not_ehs_12 : 12 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 12 ! + 1 = (13 * 13) * 2834329 := by decide
  rw [h_fact] at hdvd
  have hp13 : Nat.Prime 13 := by norm_num
  have hp283 : Nat.Prime 2834329 := by norm_num
  rcases hp.dvd_mul.mp hdvd with hdvd13_sq | hdvd283
  · rcases hp.dvd_mul.mp hdvd13_sq with hdvd13_1 | hdvd13_2
    · have : p = 13 := (hp13.eq_one_or_self_of_dvd p hdvd13_1).resolve_left hp.ne_one
      subst this; revert hmod; decide
    · have : p = 13 := (hp13.eq_one_or_self_of_dvd p hdvd13_2).resolve_left hp.ne_one
      subst this; revert hmod; decide
  · have : p = 2834329 := (hp283.eq_one_or_self_of_dvd p hdvd283).resolve_left hp.ne_one
    subst this; revert hmod; decide

private lemma ehs_8 : 8 ∈ EHSNumbers := by
  refine ⟨by decide, 61, by norm_num, ?_, ?_⟩
  · decide
  · rw [show (8 : ℕ) ! = 40320 from by decide]; norm_num

private lemma ehs_9 : 9 ∈ EHSNumbers := by
  refine ⟨by decide, 71, by norm_num, ?_, ?_⟩
  · decide
  · rw [show (9 : ℕ) ! = 362880 from by decide]; norm_num

private lemma ehs_13 : 13 ∈ EHSNumbers := by
  refine ⟨by decide, 83, by norm_num, ?_, ?_⟩
  · decide
  · rw [show (13 : ℕ) ! = 6227020800 from by decide]; norm_num

private lemma ehs_14 : 14 ∈ EHSNumbers := by
  refine ⟨by decide, 23, by norm_num, ?_, ?_⟩
  · decide
  · rw [show (14 : ℕ) ! = 87178291200 from by decide]; norm_num

private lemma ehs_15 : 15 ∈ EHSNumbers := by
  refine ⟨by decide, 59, by norm_num, ?_, ?_⟩
  · decide
  · rw [show (15 : ℕ) ! = 1307674368000 from by decide]; norm_num

private lemma ehs_16 : 16 ∈ EHSNumbers := by
  refine ⟨by decide, 61, by norm_num, ?_, ?_⟩
  · decide
  · rw [show (16 : ℕ) ! = 20922789888000 from by decide]; norm_num

private lemma ehs_17 : 17 ∈ EHSNumbers := by
  refine ⟨by decide, 661, by norm_num, ?_, ?_⟩
  · decide
  · rw [show (17 : ℕ) ! = 355687428096000 from by decide]; norm_num

private lemma count_ehs_succ_mem {m : ℕ} (h : m ∈ EHSNumbers) :
    count EHSNumbers (m + 1) = count EHSNumbers m + 1 := by
  classical
  rw [Nat.count_succ]
  split_ifs with hm
  · ring
  · exact absurd h hm

private lemma count_ehs_succ_not_mem {m : ℕ} (h : m ∉ EHSNumbers) :
    count EHSNumbers (m + 1) = count EHSNumbers m := by
  classical
  rw [Nat.count_succ]
  split_ifs with hm
  · exact absurd hm h
  · ring

private lemma count_ehs_8 : count EHSNumbers 8 = 0 := by
  classical
  rw [count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6,
      count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4,
      count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2,
      count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]

private lemma nth_ehs_0 : nth EHSNumbers 0 = 8 := by
  classical
  have := @nth_count EHSNumbers _ 8 ehs_8
  rwa [count_ehs_8] at this

private lemma count_ehs_9 : count EHSNumbers 9 = 1 := by
  classical
  rw [count_ehs_succ_mem ehs_8, count_ehs_succ_not_mem not_ehs_7,
      count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5,
      count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3,
      count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1,
      count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]

private lemma nth_ehs_1 : nth EHSNumbers 1 = 9 := by
  classical
  have := @nth_count EHSNumbers _ 9 ehs_9
  rwa [count_ehs_9] at this

private lemma count_ehs_13 : count EHSNumbers 13 = 2 := by
  classical
  rw [count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11,
      count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8,
      count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6,
      count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4,
      count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2,
      count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]

private lemma nth_ehs_2 : nth EHSNumbers 2 = 13 := by
  classical
  have := @nth_count EHSNumbers _ 13 ehs_13
  rwa [count_ehs_13] at this

private lemma count_ehs_14 : count EHSNumbers 14 = 3 := by
  classical
  rw [count_ehs_succ_mem ehs_13, count_ehs_succ_not_mem not_ehs_12,
      count_ehs_succ_not_mem not_ehs_11, count_ehs_succ_not_mem not_ehs_10,
      count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8,
      count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6,
      count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4,
      count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2,
      count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]

private lemma nth_ehs_3 : nth EHSNumbers 3 = 14 := by
  classical
  have := @nth_count EHSNumbers _ 14 ehs_14
  rwa [count_ehs_14] at this

private lemma count_ehs_15 : count EHSNumbers 15 = 4 := by
  classical
  rw [count_ehs_succ_mem ehs_14, count_ehs_succ_mem ehs_13,
      count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11,
      count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8,
      count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6,
      count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4,
      count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2,
      count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]

private lemma nth_ehs_4 : nth EHSNumbers 4 = 15 := by
  classical
  have := @nth_count EHSNumbers _ 15 ehs_15
  rwa [count_ehs_15] at this

private lemma count_ehs_16 : count EHSNumbers 16 = 5 := by
  classical
  rw [count_ehs_succ_mem ehs_15, count_ehs_succ_mem ehs_14, count_ehs_succ_mem ehs_13,
      count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11,
      count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8,
      count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6,
      count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4,
      count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2,
      count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]

private lemma nth_ehs_5 : nth EHSNumbers 5 = 16 := by
  classical
  have := @nth_count EHSNumbers _ 16 ehs_16
  rwa [count_ehs_16] at this

private lemma count_ehs_17 : count EHSNumbers 17 = 6 := by
  classical
  rw [count_ehs_succ_mem ehs_16, count_ehs_succ_mem ehs_15, count_ehs_succ_mem ehs_14,
      count_ehs_succ_mem ehs_13, count_ehs_succ_not_mem not_ehs_12,
      count_ehs_succ_not_mem not_ehs_11, count_ehs_succ_not_mem not_ehs_10,
      count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8,
      count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6,
      count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4,
      count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2,
      count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]

private lemma nth_ehs_6 : nth EHSNumbers 6 = 17 := by
  classical
  have := @nth_count EHSNumbers _ 17 ehs_17
  rwa [count_ehs_17] at this

/-- The sequence $S$ begins $8, 9, 13, 14, 15, 16, 17, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.EHSNumbers_init :
    nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  ext x
  simp only [Set.mem_image, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, ⟨hn0, hn6⟩, rfl⟩
    interval_cases n
    · left; exact nth_ehs_0
    · right; left; exact nth_ehs_1
    · right; right; left; exact nth_ehs_2
    · right; right; right; left; exact nth_ehs_3
    · right; right; right; right; left; exact nth_ehs_4
    · right; right; right; right; right; left; exact nth_ehs_5
    · right; right; right; right; right; right; exact nth_ehs_6
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by decide, nth_ehs_0⟩
    · exact ⟨1, by decide, nth_ehs_1⟩
    · exact ⟨2, by decide, nth_ehs_2⟩
    · exact ⟨3, by decide, nth_ehs_3⟩
    · exact ⟨4, by decide, nth_ehs_4⟩
    · exact ⟨5, by decide, nth_ehs_5⟩
    · exact ⟨6, by decide, nth_ehs_6⟩

/-- The sequence $P$ begins $23, 29, 59, 61, 67, 71, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_init :
    nth PillaiPrimes '' (Set.Icc 0 5) = {23, 29, 59, 61, 67, 71} := by
  ext x
  simp only [Set.mem_image, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, ⟨hn0, hn5⟩, rfl⟩
    interval_cases n
    · left; exact nth_pillai_0
    · right; left; exact nth_pillai_1
    · right; right; left; exact nth_pillai_2
    · right; right; right; left; exact nth_pillai_3
    · right; right; right; right; left; exact nth_pillai_4
    · right; right; right; right; right; exact nth_pillai_5
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by decide, nth_pillai_0⟩
    · exact ⟨1, by decide, nth_pillai_1⟩
    · exact ⟨2, by decide, nth_pillai_2⟩
    · exact ⟨3, by decide, nth_pillai_3⟩
    · exact ⟨4, by decide, nth_pillai_4⟩
    · exact ⟨5, by decide, nth_pillai_5⟩

/-- Regarding the first question, Hardy and Subbarao computed all EHS numbers up to $2^{10}$, and
write "...if this trend conditions we expect [the limit] to be around 0.5, if it exists." -/
@[category research open, AMS 11]
theorem erdos_1074.variants.EHSNumbers_one_half : EHSNumbers.HasDensity (1 / 2) := by
  sorry

end Erdos1074
