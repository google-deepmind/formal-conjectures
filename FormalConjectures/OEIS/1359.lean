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

import FormalConjecturesUtil

/-!
# Lesser of twin primes

Primes $p$ such that $p+2$ is also prime.

*References:*
- [A001359](https://oeis.org/A001359)
-/

namespace OeisA1359

/-- The $n$-th lesser twin prime, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    Nat.nth (fun p => p.Prime ∧ (p + 2).Prime) (n - 1)
  else
    0

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  norm_num[a]
  exact(((congr_arg _) (by constructor) )).trans.comp (3).nth_count (by decide)

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  delta a
  apply((congr_arg _) (by constructor) ).trans (Nat.nth_count (by decide ) )

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 11 := by
  (inhabit ℝ)
  norm_num[a]
  exact (congr_arg _ (by decide)).trans (Nat.nth_count (by decide))

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 17 := by
  simp_all[a]
  exact (congr_arg _ (by constructor) ).trans (Nat.nth_count (by decide))

open Nat

set_option maxRecDepth 100000

/-- Fixed trial divisors: all primes up to `89`. -/
def trialDivs : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89]

/-- Every element of the trial divisor list is prime. -/
@[category API, AMS 11]
theorem prime_of_mem_trialDivs : ∀ q ∈ trialDivs, q.Prime := by
  decide

/-- Every prime up to `89` is a trial divisor. -/
@[category API, AMS 11]
theorem mem_trialDivs {p : ℕ} (hpp : p.Prime) (hle : p ≤ 89) : p ∈ trialDivs := by
  interval_cases p <;> first
    | exact absurd hpp (by decide)
    | exact (by decide)

/-- Primes up to `n` (for `n ≤ 7920`), in decreasing order, via trial division
by the fixed divisor list. Correct since a composite below `7921` has a prime
factor at most `89`. -/
def primesUpTo : ℕ → List ℕ
  | 0 => []
  | (n + 1) =>
    let ps := primesUpTo n
    if (n + 1) < 2 then ps
    else if trialDivs.all (fun p => decide (p * p > n + 1 ∨ ¬ p ∣ (n + 1)))
      then (n + 1) :: ps
      else ps

/-- One unfolding step of the sieve. -/
@[category API, AMS 11]
theorem primesUpTo_succ (n : ℕ) : primesUpTo (n + 1) =
    if (n + 1) < 2 then primesUpTo n
    else if trialDivs.all (fun p => decide (p * p > n + 1 ∨ ¬ p ∣ (n + 1)))
      then (n + 1) :: primesUpTo n
      else primesUpTo n := rfl

/-- Soundness and completeness of the fast sieve below `7921`. -/
@[category API, AMS 11]
theorem primesUpTo_sound_complete (n : ℕ) (hn : n ≤ 7920) :
    (∀ p ∈ primesUpTo n, p.Prime ∧ p ≤ n) ∧
    (∀ p, p.Prime → p ≤ n → p ∈ primesUpTo n) := by
  induction n with
  | zero =>
    constructor
    · intro p hp
      simp [primesUpTo] at hp
    · intro p hpp hle
      have hp0 : p = 0 := by omega
      subst hp0
      exact absurd hpp Nat.not_prime_zero
  | succ n IH =>
    have hn' : n ≤ 7920 := by omega
    obtain ⟨IHsound, IHcomplete⟩ := IH hn'
    have hbig : n + 1 ≤ 7921 := by omega
    constructor
    · -- Soundness at level n+1.
      intro p hp
      rw [primesUpTo_succ] at hp
      by_cases h1 : (n + 1) < 2
      · rw [if_pos h1] at hp
        obtain ⟨hprime, hle⟩ := IHsound p hp
        exact ⟨hprime, by omega⟩
      · rw [if_neg h1] at hp
        by_cases h2 : trialDivs.all
            (fun p => decide (p * p > n + 1 ∨ ¬ p ∣ (n + 1))) = true
        · rw [if_pos h2] at hp
          rw [List.mem_cons] at hp
          rcases hp with rfl | hmem
          · refine ⟨?_, le_refl _⟩
            by_contra hnp
            have hne1 : n + 1 ≠ 1 := by omega
            have hmprime : Nat.Prime (Nat.minFac (n + 1)) := Nat.minFac_prime hne1
            have hmdvd : Nat.minFac (n + 1) ∣ n + 1 := Nat.minFac_dvd _
            have hmle : Nat.minFac (n + 1) ≤ n := by
              have h1 : Nat.minFac (n + 1) ≤ n + 1 := Nat.le_of_dvd (by omega) hmdvd
              have hne : Nat.minFac (n + 1) ≠ n + 1 := by
                intro heq
                rw [heq] at hmprime
                exact hnp hmprime
              omega
            have hm89 : Nat.minFac (n + 1) ≤ 89 := by
              obtain ⟨k, hk⟩ := hmdvd
              have hk2 : 2 ≤ k := by
                rcases Nat.eq_zero_or_pos k with rfl | hpos
                · simp at hk
                · by_contra hlt
                  push Not at hlt
                  have hk1 : k = 1 := by omega
                  subst hk1
                  simp at hk
                  rw [← hk] at hmprime
                  exact hnp hmprime
              have hkm : Nat.minFac (n + 1) ≤ k := by
                by_contra hlt
                push Not at hlt
                have hkdvd : k ∣ n + 1 := by
                  rw [hk]
                  exact dvd_mul_left _ _
                have hle2 : Nat.minFac (n + 1) ≤ k :=
                  Nat.minFac_le_of_dvd hk2 hkdvd
                omega
              have hge : Nat.minFac (n + 1) * Nat.minFac (n + 1) ≤ 7921 := by
                calc Nat.minFac (n + 1) * Nat.minFac (n + 1)
                    ≤ n + 1 := by
                      conv => rhs; rw [hk]
                      exact Nat.mul_le_mul (le_refl _) hkm
                  _ ≤ 7921 := hbig
              nlinarith [hge]
            have hmps : Nat.minFac (n + 1) ∈ trialDivs :=
              mem_trialDivs hmprime hm89
            have hall := (List.all_eq_true.mp h2) _ hmps
            have hdisj := of_decide_eq_true hall
            rcases hdisj with hsq | hndiv
            · -- minFac² > n+1 contradicts minFac² ≤ n+1
              obtain ⟨k, hk⟩ := hmdvd
              have hk2 : 2 ≤ k := by
                rcases Nat.eq_zero_or_pos k with rfl | hpos
                · simp at hk
                · by_contra hlt
                  push Not at hlt
                  have hk1 : k = 1 := by omega
                  subst hk1
                  simp at hk
                  rw [← hk] at hmprime
                  exact hnp hmprime
              have hkm : Nat.minFac (n + 1) ≤ k := by
                by_contra hlt
                push Not at hlt
                have hkdvd : k ∣ n + 1 := by
                  rw [hk]
                  exact dvd_mul_left _ _
                have hle2 : Nat.minFac (n + 1) ≤ k :=
                  Nat.minFac_le_of_dvd hk2 hkdvd
                omega
              have hge : Nat.minFac (n + 1) * Nat.minFac (n + 1) ≤ n + 1 := by
                conv => rhs; rw [hk]
                exact Nat.mul_le_mul (le_refl _) hkm
              omega
            · exact absurd hmdvd hndiv
          · obtain ⟨hprime, hle⟩ := IHsound p hmem
            exact ⟨hprime, by omega⟩
        · rw [if_neg h2] at hp
          obtain ⟨hprime, hle⟩ := IHsound p hp
          exact ⟨hprime, by omega⟩
    · -- Completeness at level n+1.
      intro p hpp hle
      rw [primesUpTo_succ]
      by_cases h1 : (n + 1) < 2
      · rw [if_pos h1]
        have hp2 := hpp.two_le
        have hpn : p ≤ n := by omega
        exact IHcomplete p hpp hpn
      · rw [if_neg h1]
        by_cases h2 : trialDivs.all
            (fun p => decide (p * p > n + 1 ∨ ¬ p ∣ (n + 1))) = true
        · rw [if_pos h2, List.mem_cons]
          by_cases hpn : p ≤ n
          · exact Or.inr (IHcomplete p hpp hpn)
          · left
            omega
        · rw [if_neg h2]
          have hfalse : trialDivs.all
              (fun p => decide (p * p > n + 1 ∨ ¬ p ∣ (n + 1))) = false :=
            eq_false_of_ne_true h2
          have hpn : p ≤ n := by
            by_contra hlt
            push Not at hlt
            have hpeq : p = n + 1 := by omega
            obtain ⟨q, hqps, hqf⟩ := List.all_eq_false.mp hfalse
            have hnq := of_decide_eq_false (eq_false_of_ne_true hqf)
            have hq1 : q * q ≤ n + 1 := Nat.le_of_not_gt (fun h => hnq (Or.inl h))
            have hq2 : q ∣ n + 1 := of_not_not (fun h => hnq (Or.inr h))
            have hqprime := prime_of_mem_trialDivs q hqps
            have hqp : q ∣ p := by
              rw [hpeq]
              exact hq2
            have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpp).mp hqp
            have hge : 2 ≤ n + 1 := by omega
            have hqq : q * q = (n + 1) * (n + 1) := by rw [hqe, hpeq]
            nlinarith
          exact IHcomplete p hpp hpn

/-- The sieve list has no duplicates. -/
@[category API, AMS 11]
theorem primesUpTo_nodup (n : ℕ) (hn : n ≤ 7920) : (primesUpTo n).Nodup := by
  induction n with
  | zero => simp [primesUpTo]
  | succ n IH =>
    have hn' : n ≤ 7920 := by omega
    rw [primesUpTo_succ]
    split_ifs
    · exact IH hn'
    · rw [List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨_, hle⟩ := (primesUpTo_sound_complete n hn').1 _ hmem
        omega
      · exact IH hn'
    · exact IH hn'

/-- The sieve list sees exactly the primes up to `N`. -/
@[category API, AMS 11]
theorem primesUpTo_toFinset (N : ℕ) (hN : N ≤ 7920) :
    (primesUpTo N).toFinset = Finset.filter Nat.Prime (Finset.range (N + 1)) := by
  ext m
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hm
    obtain ⟨hprime, hle⟩ := (primesUpTo_sound_complete N hN).1 m hm
    exact ⟨by omega, hprime⟩
  · intro ⟨hlt, hprime⟩
    exact (primesUpTo_sound_complete N hN).2 m hprime (by omega)

/-- Prime counts via the sieve length. -/
@[category API, AMS 11]
theorem count_eq_sieve_length (N : ℕ) (hN : N ≤ 7920) :
    Nat.count Nat.Prime (N + 1) = (primesUpTo N).length := by
  rw [Nat.count_eq_card_filter_range, ← primesUpTo_toFinset N hN,
    List.toFinset_card_of_nodup (primesUpTo_nodup N hN)]

section CountDecides
set_option maxHeartbeats 0

/-- Prime count in the interval `[7841, 7853)`: only `7841` itself. -/
@[category API, AMS 11]
theorem card_primes_Ico_7841_7853 :
    ((Finset.Ico 7841 7853).filter Nat.Prime).card = 1 := by decide

/-- The sieve reaches length `990` at `7840`. Kernel-checked finite computation. -/
@[category API, AMS 11]
theorem primesUpTo_length_7840 : (primesUpTo 7840).length = 990 := by decide

end CountDecides

section PrimeDecides
set_option maxHeartbeats 0

/-- `7841` is prime. -/
@[category API, AMS 11]
theorem prime7841 : Nat.Prime 7841 := by decide

/-- `7853` is prime. -/
@[category API, AMS 11]
theorem prime7853 : Nat.Prime 7853 := by decide

/-- Wilson residue for the `k = 991` case. -/
@[category API, AMS 11]
theorem cong991 : 7841! % 7853 = 1 := by decide

end PrimeDecides

/-- There are `990` primes below `7841`. -/
@[category API, AMS 11]
theorem count_primes_7841 : Nat.count Nat.Prime 7841 = 990 := by
  have h := count_eq_sieve_length 7840 (by norm_num)
  rw [show 7840 + 1 = 7841 from rfl, primesUpTo_length_7840] at h
  exact h

/-- The `990`-th prime (zero-indexed) is `7841`. -/
@[category API, AMS 11]
theorem nth_prime_990 : Nat.nth Nat.Prime 990 = 7841 := by
  have h := Nat.nth_count prime7841
  rwa [count_primes_7841] at h

/-- There are `991` primes below `7853`. -/
@[category API, AMS 11]
theorem count_primes_7853 : Nat.count Nat.Prime 7853 = 991 := by
  have u : Finset.Ico 0 7841 ∪ Finset.Ico 7841 7853 = Finset.Ico 0 7853 :=
    Finset.Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)
  have e : Finset.range 7853 = Finset.range 7841 ∪ Finset.Ico 7841 7853 := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, ← u]
  have d : Disjoint ((Finset.range 7841).filter Nat.Prime)
      ((Finset.Ico 7841 7853).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx1 hx2
    obtain ⟨hx1r, -⟩ := hx1
    obtain ⟨hx2l, -⟩ := hx2
    omega
  have c7841 : ((Finset.range 7841).filter Nat.Prime).card = 990 := by
    rw [← Nat.count_eq_card_filter_range]
    exact count_primes_7841
  rw [Nat.count_eq_card_filter_range, e, Finset.filter_union,
    Finset.card_union_of_disjoint d, c7841, card_primes_Ico_7841_7853]


/-- The `991`-st prime (zero-indexed) is `7853`. -/
@[category API, AMS 11]
theorem nth_prime_991 : Nat.nth Nat.Prime 991 = 7853 := by
  have h := Nat.nth_count prime7853
  rwa [count_primes_7853] at h

/-- No prime lies strictly between consecutive `Nat.nth` primes. -/
@[category API, AMS 11]
theorem no_prime_between (k : ℕ) :
    ¬ ∃ r : ℕ, r.Prime ∧ Nat.nth Nat.Prime k < r ∧ r < Nat.nth Nat.Prime (k + 1) := by
  rintro ⟨r, hrp, har, hrb⟩
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime k) = k :=
    Nat.count_nth_of_infinite hinf k
  have h2 : Nat.count Nat.Prime (Nat.nth Nat.Prime (k + 1)) = k + 1 :=
    Nat.count_nth_of_infinite hinf (k + 1)
  have hpk : (Nat.nth Nat.Prime k).Prime := Nat.prime_nth_prime k
  have e1 : Nat.count Nat.Prime (Nat.nth Nat.Prime k + 1) = k + 1 := by
    rw [Nat.count_succ, if_pos hpk, h1]
  have e2 : Nat.count Nat.Prime (r + 1) = Nat.count Nat.Prime r + 1 := by
    rw [Nat.count_succ, if_pos hrp]
  have e1le : Nat.nth Nat.Prime k + 1 ≤ r := by omega
  have e2le : r + 1 ≤ Nat.nth Nat.Prime (k + 1) := by omega
  have c1 := Nat.count_monotone (p := Nat.Prime) e1le
  have c2 := Nat.count_monotone (p := Nat.Prime) e2le
  omega

-- Helper: Nat factorial splitting.
/-- Splitting `(q - 1)!` at `p`. -/
@[category API, AMS 11]
theorem factorial_split (p q : ℕ) (h : p + 2 ≤ q) :
    (q - 1)! = p ! * (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) * (q - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, q - 1 = p + m := ⟨q - 1 - p, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hq2 : q - 2 = p + m - 1 := by omega
  rw [hm, hq2]
  have step1 : (p + m)! = ∏ i ∈ Finset.range (p + m), (i + 1) := by
    rw [Finset.prod_range_add_one_eq_factorial]
  rw [step1, Finset.prod_range_add (fun i => i + 1) p m]
  have hfac : ∏ i ∈ Finset.range p, (i + 1) = p ! := by
    rw [Finset.prod_range_add_one_eq_factorial]
  rw [hfac]
  have hbij : ∏ x ∈ Finset.range m, (p + x + 1) = ∏ i ∈ Finset.Icc (p + 1) (p + m), i := by
    apply Finset.prod_bij (fun x _ => p + x + 1)
    · intro x hx
      simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢
      omega
    · intro x1 _ x2 _ h12
      omega
    · intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
      exact ⟨i - (p + 1), Finset.mem_range.mpr (by omega), by omega⟩
    · intro x _
      rfl
  rw [hbij]
  have hpm : p + m - 1 + 1 = p + m := by omega
  have htop : ∏ i ∈ Finset.Icc (p + 1) (p + m), i
      = (∏ i ∈ Finset.Icc (p + 1) (p + m - 1), i) * (p + m) := by
    have h2 := Finset.prod_Icc_succ_top (show p + 1 ≤ (p + m - 1) + 1 by omega) (fun i => i)
    rwa [hpm] at h2
  rw [htop, mul_assoc]

-- Helper: the splitting in ZMod q (term-wise cast product).
/-- The factorial splitting, cast into `ZMod q`. -/
@[category API, AMS 11]
theorem wilson_split (p q : ℕ) (h : p + 2 ≤ q) :
    ((q - 1)! : ZMod q)
      = (p ! : ZMod q) * (∏ i ∈ Finset.Icc (p + 1) (q - 2), ((i : ℕ) : ZMod q))
        * (((q - 1 : ℕ)) : ZMod q) := by
  have hnat := factorial_split p q h
  have hcast := congrArg (fun t : ℕ => (t : ZMod q)) hnat
  simpa using hcast

-- The k = 991 product value, from Wilson + the 7841! computation.
/-- The `k = 991` middle product equals `1`. -/
@[category API, AMS 11]
theorem W991 :
    (∏ i ∈ Finset.Icc (7841 + 1) (7853 - 2), i) ≡ 1 [MOD 7853] := by
  have hwil : ((7853 - 1)! : ZMod 7853) = -1 := @ZMod.wilsons_lemma 7853 ⟨prime7853⟩
  have hsplit := wilson_split 7841 7853 (by norm_num)
  have hqm1 : ((((7853 - 1 : ℕ))) : ZMod 7853) = -1 := by
    rw [Nat.cast_sub (by norm_num), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have e : (7841! : ZMod 7853)
      * (∏ i ∈ Finset.Icc ((7841 + 1 : ℕ)) ((7853 - 2 : ℕ)), (i : ZMod 7853)) * (-1) = -1 := by
    have e2 := hsplit.symm.trans hwil
    rwa [hqm1] at e2
  have key : (7841! : ZMod 7853)
      * (∏ i ∈ Finset.Icc ((7841 + 1 : ℕ)) ((7853 - 2 : ℕ)), (i : ZMod 7853)) = 1 := by
    generalize (7841! : ZMod 7853) = F at e ⊢
    linear_combination -e
  have f : (7841! : ZMod 7853) = 1 := by
    have hmod : 7841! ≡ 1 [MOD 7853] := by
      have h1 : 7841! % 7853 ≡ 7841! [MOD 7853] := Nat.mod_modEq _ _
      rw [cong991] at h1
      exact h1.symm
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    simpa using h2
  rw [f, one_mul] at key
  have hcast : ((∏ i ∈ Finset.Icc ((7841 + 1 : ℕ)) ((7853 - 2 : ℕ)), i : ℕ) : ZMod 7853)
      = ∏ i ∈ Finset.Icc ((7841 + 1 : ℕ)) ((7853 - 2 : ℕ)), (i : ZMod 7853) := by
    rw [Nat.cast_prod]
  rw [← hcast] at key
  have h1c : ((1 : ℕ) : ZMod 7853) = 1 := Nat.cast_one
  rw [← h1c] at key
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mp key
  simpa using h3

-- Core lemma: everything abstracted except the two computations-fed hypotheses.
/-- Abstracted twin-prime congruence criterion. -/
@[category API, AMS 11]
theorem congruence_core (p q k : ℕ) (hpk : p.Prime) (hqk : q.Prime) (hpq : p < q) (hp3 : 3 ≤ p)
    (hconsec : ¬ ∃ r : ℕ, r.Prime ∧ p < r ∧ r < q)
    (h991case : k = 991 → p = 7841 ∧ q = 7853)
    (hW991 : p = 7841 → q = 7853 →
      (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q]) :
    p ! ≡ 1 [MOD q] ↔
      ((p + 2).Prime ∨ k = 991 ∨
        (q - p > 2 ∧ (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q])) := by
  have hgap : p + 2 ≤ q := by
    by_contra h
    push Not at h
    have hqp1 : q = p + 1 := by omega
    obtain ⟨t, ht⟩ := hpk.odd_of_ne_two (by omega)
    rcases hqk.eq_two_or_odd with h2 | h2 <;> omega
  have hwil : ((q - 1)! : ZMod q) = -1 := @ZMod.wilsons_lemma q ⟨hqk⟩
  have hsplit := wilson_split p q hgap
  have hqm1 : ((((q - 1 : ℕ))) : ZMod q) = -1 := by
    have hq1 : 1 ≤ q := by omega
    rw [Nat.cast_sub hq1, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have e : (p ! : ZMod q) * (∏ i ∈ Finset.Icc (p + 1) (q - 2), (i : ZMod q)) * (-1) = -1 := by
    have e2 := hsplit.symm.trans hwil
    rwa [hqm1] at e2
  have key : (p ! : ZMod q) * (∏ i ∈ Finset.Icc (p + 1) (q - 2), (i : ZMod q)) = 1 := by
    linear_combination -e
  have keyIff : ((p ! : ZMod q) = 1 ↔
      (∏ i ∈ Finset.Icc (p + 1) (q - 2), (i : ZMod q)) = 1) := by
    constructor
    · intro h1
      rw [h1, one_mul] at key
      exact key
    · intro hW1
      rw [hW1, mul_one] at key
      exact key
  have tCong : ((p ! : ZMod q) = 1 ↔ p ! ≡ 1 [MOD q]) := by
    have h := ZMod.natCast_eq_natCast_iff (p !) 1 q
    simpa using h
  have tW : ((∏ i ∈ Finset.Icc (p + 1) (q - 2), (i : ZMod q)) = 1 ↔
      (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q]) := by
    have h := ZMod.natCast_eq_natCast_iff (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) 1 q
    rw [Nat.cast_prod, Nat.cast_one] at h
    exact h
  have main : (p ! ≡ 1 [MOD q]) ↔ ((∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q]) :=
    tCong.symm.trans (keyIff.trans tW)
  have h2cases : q - p = 2 ∨ q - p > 2 := by omega
  rcases h2cases with hgap2 | hgap3
  · -- gap = 2: both sides true
    have hW1 : (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) = 1 := by
      have hempty : Finset.Icc (p + 1) (q - 2) = ∅ := by
        rw [Finset.Icc_eq_empty (by omega : ¬ p + 1 ≤ q - 2)]
      rw [hempty, Finset.prod_empty]
    have hW : (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q] := by
      rw [hW1]
    have hRHS : (p + 2).Prime ∨ k = 991 ∨
        (q - p > 2 ∧ (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q]) := by
      left
      have hpq2 : p + 2 = q := by omega
      rwa [hpq2]
    have hLHS : p ! ≡ 1 [MOD q] := main.mpr hW
    exact iff_of_true hLHS hRHS
  · -- gap > 2
    have hntwin : ¬ (p + 2).Prime := by
      intro htwin
      exact hconsec ⟨p + 2, htwin, by omega, by omega⟩
    rcases eq_or_ne k 991 with hk991 | hk991'
    · -- k = 991: RHS true; LHS via computation
      obtain ⟨rfl, rfl⟩ := h991case hk991
      have hLHS : 7841! ≡ 1 [MOD 7853] := main.mpr (hW991 rfl rfl)
      exact iff_of_true hLHS (Or.inr (Or.inl hk991))
    · have hRHS : ((p + 2).Prime ∨ k = 991 ∨
            (q - p > 2 ∧ (∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q])) ↔
          ((∏ i ∈ Finset.Icc (p + 1) (q - 2), i) ≡ 1 [MOD q]) := by
        constructor
        · rintro (h | h | ⟨-, h⟩)
          · exact absurd h hntwin
          · exact absurd h hk991'
          · exact h
        · intro h
          exact Or.inr (Or.inr ⟨hgap3, h⟩)
      exact main.trans hRHS.symm

-- Application to consecutive nth primes.
/-- The conjecture unfolded for consecutive `Nat.nth` primes. -/
@[category API, AMS 11]
theorem conjecture_main (k : ℕ) (hk : 1 < k) :
    (Nat.nth Nat.Prime (k - 1))! ≡ 1 [MOD Nat.nth Nat.Prime k] ↔
      ((Nat.nth Nat.Prime (k - 1) + 2).Prime ∨ k = 991 ∨
        (Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1) > 2 ∧
          ∏ i ∈ Finset.Icc (Nat.nth Nat.Prime (k - 1) + 1) (Nat.nth Nat.Prime k - 2), i
            ≡ 1 [MOD Nat.nth Nat.Prime k])) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hpk : (Nat.nth Nat.Prime (k - 1)).Prime := Nat.prime_nth_prime (k - 1)
  have hqk : (Nat.nth Nat.Prime k).Prime := Nat.prime_nth_prime k
  have hkk : k - 1 < k := by omega
  have hpq : Nat.nth Nat.Prime (k - 1) < Nat.nth Nat.Prime k :=
    (Nat.nth_lt_nth hinf).mpr hkk
  have hp3 : 3 ≤ Nat.nth Nat.Prime (k - 1) := by
    have h1k : 1 ≤ k - 1 := by omega
    have hle := (Nat.nth_le_nth hinf).mpr h1k
    rwa [Nat.nth_prime_one_eq_three] at hle
  have hconsec : ¬ ∃ r : ℕ, r.Prime ∧ Nat.nth Nat.Prime (k - 1) < r ∧ r < Nat.nth Nat.Prime k := by
    have e : (k - 1) + 1 = k := by omega
    have h := no_prime_between (k - 1)
    rwa [e] at h
  have h991case : k = 991 → Nat.nth Nat.Prime (k - 1) = 7841 ∧ Nat.nth Nat.Prime k = 7853 := by
    intro hk991
    have e1 : k - 1 = 990 := by omega
    rw [e1]
    exact ⟨nth_prime_990, by rw [hk991]; exact nth_prime_991⟩
  have hW991 : Nat.nth Nat.Prime (k - 1) = 7841 → Nat.nth Nat.Prime k = 7853 →
      (∏ i ∈ Finset.Icc (Nat.nth Nat.Prime (k - 1) + 1) (Nat.nth Nat.Prime k - 2), i)
        ≡ 1 [MOD Nat.nth Nat.Prime k] := by
    intro h1 h2
    rw [h1, h2]
    exact W991
  exact congruence_core _ _ k hpk hqk hpq hp3 hconsec h991case hW991

/--
Primes $p_k$ such that $p_k! \equiv 1 \pmod{p_{k+1}}$ with the exception of $p_{991} = 7841$ and
other unknown primes $p_k$ for which $(p_k+1)(p_k+2)\cdots(p_{k+1}-2) \equiv 1 \pmod{p_{k+1}}$
where $p_{k+1} - p_k > 2$.
-/
@[category research solved, AMS 11]
theorem conjecture (k : ℕ) (hk : k > 1) :
    let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])) := by
  exact conjecture_main k hk

end OeisA1359
