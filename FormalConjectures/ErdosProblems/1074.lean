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

noncomputable instance : DecidablePred EHSNumbers := Classical.decPred _
noncomputable instance : DecidablePred PillaiPrimes := Classical.decPred _



def isPillaiPrime (p : ℕ) : Bool :=
  (p.minFac == p) && (decide (2 ≤ p)) && (List.range p).any (fun m => decide (1 ≤ m) && ((p - 1) % m != 0) && ((m ! + 1) % p == 0))

lemma pillai_m_lt_p {p m : ℕ} (hp : p.Prime) (hm : p ∣ m ! + 1) : m < p := by
  by_contra! h
  have h1 : p ∣ m ! := dvd_factorial hp.pos h
  have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hm
  exact hp.not_dvd_one h2

lemma pillai_dec_eq (p : ℕ) : p ∈ PillaiPrimes ↔ isPillaiPrime p = true := by
  dsimp [PillaiPrimes, isPillaiPrime]
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  rw [prime_def_minFac]
  simp only [decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.mem_range]
  constructor
  · rintro ⟨⟨h2, hmF⟩, ⟨m, hm1, hm2, hm3⟩⟩
    have hp : p.Prime := by rw [prime_def_minFac]; exact ⟨h2, hmF⟩
    have h_lt : m < p := pillai_m_lt_p hp hm3
    refine ⟨⟨hmF, h2⟩, ⟨m, h_lt, ⟨hm1, ?_⟩, ?_⟩⟩
    · intro h_mod
      apply hm2
      have hp1 : 1 ≤ p := by omega
      have hdvd : m ∣ p - 1 := Nat.dvd_of_mod_eq_zero h_mod
      exact ((Nat.modEq_iff_dvd' hp1).mpr hdvd).symm
    · rwa [← Nat.dvd_iff_mod_eq_zero]
  · rintro ⟨⟨hmF, h2⟩, m, hm_in, ⟨hm1, hm2⟩, hm3⟩
    refine ⟨⟨h2, hmF⟩, m, hm1, ?_, ?_⟩
    · intro h_mod
      apply hm2
      have hp1 : 1 ≤ p := by omega
      have hdvd : m ∣ p - 1 := (Nat.modEq_iff_dvd' hp1).mp h_mod.symm
      exact Nat.mod_eq_zero_of_dvd hdvd
    · rwa [Nat.dvd_iff_mod_eq_zero]

lemma count_pillai (n : ℕ) : count PillaiPrimes n = (List.range n).countP (fun p => isPillaiPrime p) := by
  classical
  rw [count]
  apply List.countP_congr
  intro a _
  simp only [decide_eq_true_eq]
  exact pillai_dec_eq a

lemma pillai_23 : 23 ∈ PillaiPrimes := by rw [pillai_dec_eq]; native_decide
lemma c_23 : count PillaiPrimes 23 = 0 := by rw [count_pillai]; native_decide
lemma nth_pillai_0 : nth PillaiPrimes 0 = 23 := by
  classical
  have := @nth_count PillaiPrimes _ 23 pillai_23
  rwa [c_23] at this

lemma pillai_29 : 29 ∈ PillaiPrimes := by rw [pillai_dec_eq]; native_decide
lemma c_29 : count PillaiPrimes 29 = 1 := by rw [count_pillai]; native_decide
lemma nth_pillai_1 : nth PillaiPrimes 1 = 29 := by
  classical
  have := @nth_count PillaiPrimes _ 29 pillai_29
  rwa [c_29] at this

lemma pillai_59 : 59 ∈ PillaiPrimes := by rw [pillai_dec_eq]; native_decide
lemma c_59 : count PillaiPrimes 59 = 2 := by rw [count_pillai]; native_decide
lemma nth_pillai_2 : nth PillaiPrimes 2 = 59 := by
  classical
  have := @nth_count PillaiPrimes _ 59 pillai_59
  rwa [c_59] at this

lemma pillai_61 : 61 ∈ PillaiPrimes := by rw [pillai_dec_eq]; native_decide
lemma c_61 : count PillaiPrimes 61 = 3 := by rw [count_pillai]; native_decide
lemma nth_pillai_3 : nth PillaiPrimes 3 = 61 := by
  classical
  have := @nth_count PillaiPrimes _ 61 pillai_61
  rwa [c_61] at this

lemma pillai_67 : 67 ∈ PillaiPrimes := by rw [pillai_dec_eq]; native_decide
lemma c_67 : count PillaiPrimes 67 = 4 := by rw [count_pillai]; native_decide
lemma nth_pillai_4 : nth PillaiPrimes 4 = 67 := by
  classical
  have := @nth_count PillaiPrimes _ 67 pillai_67
  rwa [c_67] at this

lemma pillai_71 : 71 ∈ PillaiPrimes := by rw [pillai_dec_eq]; native_decide
lemma c_71 : count PillaiPrimes 71 = 5 := by rw [count_pillai]; native_decide
lemma nth_pillai_5 : nth PillaiPrimes 5 = 71 := by
  classical
  have := @nth_count PillaiPrimes _ 71 pillai_71
  rwa [c_71] at this

def checkEHS (m p : ℕ) : Bool :=
  p.minFac == p && decide (2 ≤ p) && decide (p % m != 1 % m) && decide ((m ! + 1) % p == 0)

lemma checkEHS_eq {m p : ℕ} : checkEHS m p = true ↔ p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1 := by
  dsimp [checkEHS]
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
  rw [prime_def_minFac]
  simp only [bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨hmF, h2⟩, hmod⟩, hdvd⟩
    refine ⟨⟨h2, hmF⟩, ?_, Nat.dvd_of_mod_eq_zero hdvd⟩
    intro h_eq
    exact hmod h_eq
  · rintro ⟨⟨h2, hmF⟩, hmod, hdvd⟩
    refine ⟨⟨⟨hmF, h2⟩, ?_⟩, Nat.mod_eq_zero_of_dvd hdvd⟩
    intro h_eq
    exact hmod h_eq

lemma not_ehs_small (m : ℕ) (h : (List.range (m ! + 2)).all (fun p => !(checkEHS m p)) = true) : m ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h1 : p ∣ m ! + 1 := hdvd
  have hp_le : p < m ! + 2 := by
    have h_pos : 0 < m ! + 1 := Nat.succ_pos _
    have : p ≤ m ! + 1 := Nat.le_of_dvd h_pos h1
    omega
  have h_mem : p ∈ List.range (m ! + 2) := List.mem_range.mpr hp_le
  have h_all := List.all_eq_true.mp h p h_mem
  rw [Bool.not_eq_true'] at h_all
  have h_check := checkEHS_eq.mpr ⟨hp, hmod, hdvd⟩
  rw [h_check] at h_all
  contradiction
  
lemma not_ehs_0 : 0 ∉ EHSNumbers := by intro h; cases h.1

lemma not_ehs_10 : 10 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 10 ! + 1 = 11 * 329891 := by decide
  rw [h_fact] at hdvd
  have hp11 : Nat.Prime 11 := by norm_num
  have hp329 : Nat.Prime 329891 := by norm_num
  rcases (hp.dvd_mul.mp hdvd) with hdvd11 | hdvd329
  · have : p = 11 := (hp11.eq_one_or_self_of_dvd p hdvd11).resolve_left hp.ne_one
    subst this
    revert hmod; decide
  · have : p = 329891 := (hp329.eq_one_or_self_of_dvd p hdvd329).resolve_left hp.ne_one
    subst this
    revert hmod; decide

lemma not_ehs_11 : 11 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 11 ! + 1 = 39916801 := by decide
  rw [h_fact] at hdvd
  have hp39 : Nat.Prime 39916801 := by norm_num
  have : p = 39916801 := (hp39.eq_one_or_self_of_dvd p hdvd).resolve_left hp.ne_one
  subst this
  revert hmod; decide

lemma not_ehs_12 : 12 ∉ EHSNumbers := by
  intro ⟨_, p, hp, hmod, hdvd⟩
  have h_fact : 12 ! + 1 = (13 * 13) * 2834329 := by decide
  rw [h_fact] at hdvd
  have hp13 : Nat.Prime 13 := by norm_num
  have hp283 : Nat.Prime 2834329 := by norm_num
  rcases hp.dvd_mul.mp hdvd with hdvd13_sq | hdvd283
  · rcases hp.dvd_mul.mp hdvd13_sq with hdvd13_1 | hdvd13_2
    · have : p = 13 := (hp13.eq_one_or_self_of_dvd p hdvd13_1).resolve_left hp.ne_one
      subst this
      revert hmod; decide
    · have : p = 13 := (hp13.eq_one_or_self_of_dvd p hdvd13_2).resolve_left hp.ne_one
      subst this
      revert hmod; decide
  · have : p = 2834329 := (hp283.eq_one_or_self_of_dvd p hdvd283).resolve_left hp.ne_one
    subst this
    revert hmod; decide

lemma not_ehs_1 : 1 ∉ EHSNumbers := by
  apply not_ehs_small; native_decide
lemma not_ehs_2 : 2 ∉ EHSNumbers := by
  apply not_ehs_small; native_decide
lemma not_ehs_3 : 3 ∉ EHSNumbers := by
  apply not_ehs_small; native_decide
lemma not_ehs_4 : 4 ∉ EHSNumbers := by
  apply not_ehs_small; native_decide
lemma not_ehs_5 : 5 ∉ EHSNumbers := by
  apply not_ehs_small; native_decide
lemma not_ehs_6 : 6 ∉ EHSNumbers := by
  apply not_ehs_small; native_decide
lemma not_ehs_7 : 7 ∉ EHSNumbers := by
  apply not_ehs_small; native_decide
lemma ehs_8 : 8 ∈ EHSNumbers := by
  have : checkEHS 8 61 = true := by native_decide
  exact ⟨by decide, 61, checkEHS_eq.mp this⟩
lemma ehs_9 : 9 ∈ EHSNumbers := by
  have : checkEHS 9 71 = true := by native_decide
  exact ⟨by decide, 71, checkEHS_eq.mp this⟩
lemma ehs_13 : 13 ∈ EHSNumbers := by
  have : checkEHS 13 83 = true := by native_decide
  exact ⟨by decide, 83, checkEHS_eq.mp this⟩
lemma ehs_14 : 14 ∈ EHSNumbers := by
  have : checkEHS 14 23 = true := by native_decide
  exact ⟨by decide, 23, checkEHS_eq.mp this⟩
lemma ehs_15 : 15 ∈ EHSNumbers := by
  have : checkEHS 15 59 = true := by native_decide
  exact ⟨by decide, 59, checkEHS_eq.mp this⟩
lemma ehs_16 : 16 ∈ EHSNumbers := by
  have : checkEHS 16 61 = true := by native_decide
  exact ⟨by decide, 61, checkEHS_eq.mp this⟩
lemma ehs_17 : 17 ∈ EHSNumbers := by
  have : checkEHS 17 661 = true := by native_decide
  exact ⟨by decide, 661, checkEHS_eq.mp this⟩

lemma count_ehs_succ_mem {m : ℕ} (h : m ∈ EHSNumbers) : count EHSNumbers (m + 1) = count EHSNumbers m + 1 := by
  classical
  rw [Nat.count_succ]
  simp [h]
lemma count_ehs_succ_not_mem {m : ℕ} (h : m ∉ EHSNumbers) : count EHSNumbers (m + 1) = count EHSNumbers m := by
  classical
  rw [Nat.count_succ]
  simp [h]

lemma count_ehs_8 : count EHSNumbers 8 = 0 := by
  classical
  rw [count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]
lemma nth_ehs_0 : nth EHSNumbers 0 = 8 := by
  classical
  have := @nth_count EHSNumbers _ 8 ehs_8
  rwa [count_ehs_8] at this

lemma count_ehs_9 : count EHSNumbers 9 = 1 := by
  classical
  rw [count_ehs_succ_mem ehs_8, count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]
lemma nth_ehs_1 : nth EHSNumbers 1 = 9 := by
  classical
  have := @nth_count EHSNumbers _ 9 ehs_9
  rwa [count_ehs_9] at this

lemma count_ehs_13 : count EHSNumbers 13 = 2 := by
  classical
  rw [count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11, count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8, count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]
lemma nth_ehs_2 : nth EHSNumbers 2 = 13 := by
  classical
  have := @nth_count EHSNumbers _ 13 ehs_13
  rwa [count_ehs_13] at this

lemma count_ehs_14 : count EHSNumbers 14 = 3 := by
  classical
  rw [count_ehs_succ_mem ehs_13, count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11, count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8, count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]
lemma nth_ehs_3 : nth EHSNumbers 3 = 14 := by
  classical
  have := @nth_count EHSNumbers _ 14 ehs_14
  rwa [count_ehs_14] at this

lemma count_ehs_15 : count EHSNumbers 15 = 4 := by
  classical
  rw [count_ehs_succ_mem ehs_14, count_ehs_succ_mem ehs_13, count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11, count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8, count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]
lemma nth_ehs_4 : nth EHSNumbers 4 = 15 := by
  classical
  have := @nth_count EHSNumbers _ 15 ehs_15
  rwa [count_ehs_15] at this

lemma count_ehs_16 : count EHSNumbers 16 = 5 := by
  classical
  rw [count_ehs_succ_mem ehs_15, count_ehs_succ_mem ehs_14, count_ehs_succ_mem ehs_13, count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11, count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8, count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]
lemma nth_ehs_5 : nth EHSNumbers 5 = 16 := by
  classical
  have := @nth_count EHSNumbers _ 16 ehs_16
  rwa [count_ehs_16] at this

lemma count_ehs_17 : count EHSNumbers 17 = 6 := by
  classical
  rw [count_ehs_succ_mem ehs_16, count_ehs_succ_mem ehs_15, count_ehs_succ_mem ehs_14, count_ehs_succ_mem ehs_13, count_ehs_succ_not_mem not_ehs_12, count_ehs_succ_not_mem not_ehs_11, count_ehs_succ_not_mem not_ehs_10, count_ehs_succ_mem ehs_9, count_ehs_succ_mem ehs_8, count_ehs_succ_not_mem not_ehs_7, count_ehs_succ_not_mem not_ehs_6, count_ehs_succ_not_mem not_ehs_5, count_ehs_succ_not_mem not_ehs_4, count_ehs_succ_not_mem not_ehs_3, count_ehs_succ_not_mem not_ehs_2, count_ehs_succ_not_mem not_ehs_1, count_ehs_succ_not_mem not_ehs_0, Nat.count_zero]
lemma nth_ehs_6 : nth EHSNumbers 6 = 17 := by
  classical
  have := @nth_count EHSNumbers _ 17 ehs_17
  rwa [count_ehs_17] at this


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
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/1074", AMS 11]
theorem erdos_1074.variants.EHSNumbers_infinite : EHSNumbers.Infinite := by
  sorry

/-- Erdős, Hardy, and Subbarao proved that $P$ is infinite. -/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/1074", AMS 11]
theorem erdos_1074.variants.PillaiPrimes_infinite : PillaiPrimes.Infinite := by
  sorry

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
