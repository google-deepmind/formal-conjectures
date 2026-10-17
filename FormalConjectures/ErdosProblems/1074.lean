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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1074

*Reference:* [erdosproblems.com/1074](https://www.erdosproblems.com/1074)
-/

@[expose] public section

namespace Erdos1074

open scoped Nat
open Nat

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
abbrev EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes $p$ such that there exists an $m \ge 1$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$-/
abbrev PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m ≥ 1, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

@[category test, AMS 11]
theorem two_not_mem_pillaiPrimes : ¬ 2 ∈ PillaiPrimes := by
  norm_num
  intro m hm h
  exact (Nat.dvd_factorial (by decide) (hm.lt_of_ne (by bound))).modEq_zero_nat.add_right 1

@[category test, AMS 11]
theorem twentyThree_mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  norm_num
  use 14
  decide

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. Does
$$
  \lim\frac{|S\cap[1, x]|}{x}
$$
exist? -/
@[category research open, question, AMS 11]
theorem erdos_1074.parts.i : ∃ c, EHSNumbers.HasDensity c := by
  sorry

def erdos_1074.parts.ii.answer : ℝ := sorry

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. What is
$$
  \lim\frac{|S\cap[1, x]|}{x}?
$$ -/
@[category research open, question value, AMS 11]
theorem erdos_1074.parts.ii : EHSNumbers.HasDensity erdos_1074.parts.ii.answer := by
  sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then does
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}
$$
exist? -/
@[category research open, question, AMS 11]
theorem erdos_1074.parts.iii : ∃ c, PillaiPrimes.HasDensity c {p | p.Prime} := by
  sorry

def erdos_1074.parts.iv.answer : ℝ := sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then what is
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}?
$$ -/
@[category research open, question value, AMS 11]
theorem erdos_1074.parts.iv :
    PillaiPrimes.HasDensity erdos_1074.parts.iv.answer {p | p.Prime} := by
  sorry

/-- Pillai [Pi30] raised the question of whether there exist any primes in $P$. This was answered
by Chowla, who noted that, for example, $14! + 1 \equiv 18! + 1 \equiv 0 \pmod{23}$. -/
@[category test, AMS 11]
theorem erdos_1074.variants.mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  norm_num
  exact ⟨14, by decide⟩

/--
Erdős, Hardy, and Subbarao proved that $S$ is infinite.

Formal proof linked here provided by AlphaProof.
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mzhorvath1/formal-conjectures/blob/3dec597bd1a73778760b761712a1fc5fb24bc5d7/FormalConjectures/ErdosProblems/1074.lean#L99"]
theorem erdos_1074.variants.EHSNumbers_infinite : EHSNumbers.Infinite := by
  sorry

/-- Erdős, Hardy, and Subbarao proved that $P$ is infinite. -/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/anatoliiohorodnyk/lean-fc-proofs/blob/5da9642575b26c2c816a49bcb56b33fed5456619/Proofs/T_Erdos1074_erdos_1074_variants_PillaiPrimes_infinite.lean#L178"]
theorem erdos_1074.variants.PillaiPrimes_infinite : PillaiPrimes.Infinite := by
  sorry

/-- If a set agrees with a finset `S` below `N`, then `nth` agrees with `S` on its elements. -/
@[category API, AMS 11]
lemma nth_count_eq_of_mem_iff {P : Set ℕ} {S : Finset ℕ} {N : ℕ}
    (h : ∀ k < N, k ∈ P ↔ k ∈ S) {v : ℕ} (hv : v ∈ S) (hvN : v < N) :
    nth P (count (· ∈ S) v) = v := by
  classical
  have hc : count (· ∈ P) v = count (· ∈ S) v := by
    simp only [count_eq_card_filter_range]
    exact congrArg _ (Finset.filter_congr fun k hk => h k ((Finset.mem_range.1 hk).trans hvN))
  rw [← hc]
  exact nth_count (p := (· ∈ P)) ((h v hvN).2 hv)

@[category API, AMS 11]
lemma mem_EHSNumbers_iff (m : ℕ) :
    m ∈ EHSNumbers ↔ 1 ≤ m ∧ ∃ p ∈ (m ! + 1).primeFactorsList, ¬p ≡ 1 [MOD m] := by
  simp only [Set.mem_ofPred_eq, mem_primeFactorsList (succ_ne_zero _)]
  grind

@[category API, AMS 11]
lemma mem_EHSNumbers_of_lt {k : ℕ} (hk : k < 18) :
    k ∈ EHSNumbers ↔ k ∈ ({8, 9, 13, 14, 15, 16, 17} : Finset ℕ) := by
  by_cases h14 : k = 14
  · -- $14! + 1 = 23 \cdot 3790360487$; avoid certifying the large prime factor.
    subst h14
    refine iff_of_true ?_ (by simp)
    exact ⟨by norm_num, 23, by norm_num, by decide, by norm_num [Nat.factorial]⟩
  rw [mem_EHSNumbers_iff]
  interval_cases k <;> first | exact absurd rfl h14 | simp [Nat.factorial, Nat.ModEq]

/-- A prime $p$ with $p \mid m! + 1$ satisfies $m < p$, so membership in `PillaiPrimes` is
decidable. -/
@[category API, AMS 11]
lemma mem_PillaiPrimes_iff (p : ℕ) :
    p ∈ PillaiPrimes ↔ p.Prime ∧ ∃ m ∈ Finset.Ico 1 p, ¬p % m = 1 % m ∧ (m ! + 1) % p = 0 := by
  simp only [Set.mem_ofPred_eq, Finset.mem_Ico, Nat.ModEq, Nat.dvd_iff_mod_eq_zero]
  refine and_congr_right fun hp =>
    ⟨fun ⟨m, hm, h⟩ => ⟨m, ⟨hm, ?_⟩, h⟩, fun ⟨m, hm, h⟩ => ⟨m, hm.1, h⟩⟩
  by_contra hpm
  have := (Nat.dvd_add_right (Nat.dvd_factorial hp.pos (not_lt.1 hpm))).1
    (Nat.dvd_of_mod_eq_zero h.2)
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

@[category API, AMS 11]
lemma mem_PillaiPrimes_of_lt {p : ℕ} (hp : p < 72) :
    p ∈ PillaiPrimes ↔ p ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ) := by
  rw [mem_PillaiPrimes_iff]
  revert p
  decide +kernel

/-- The sequence $S$ begins $8, 9, 13, 14, 15, 16, 17, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.EHSNumbers_init :
    nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  have h := fun v hv => nth_count_eq_of_mem_iff (fun _ => mem_EHSNumbers_of_lt) (v := v) hv
  have h0 : nth EHSNumbers 0 = 8 := h 8 (by simp) (by norm_num)
  have h1 : nth EHSNumbers 1 = 9 := h 9 (by simp) (by norm_num)
  have h2 : nth EHSNumbers 2 = 13 := h 13 (by simp) (by norm_num)
  have h3 : nth EHSNumbers 3 = 14 := h 14 (by simp) (by norm_num)
  have h4 : nth EHSNumbers 4 = 15 := h 15 (by simp) (by norm_num)
  have h5 : nth EHSNumbers 5 = 16 := h 16 (by simp) (by norm_num)
  have h6 : nth EHSNumbers 6 = 17 := h 17 (by simp) (by norm_num)
  ext x
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    interval_cases i <;> simp [h0, h1, h2, h3, h4, h5, h6]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, by simp, h0⟩, ⟨1, by simp, h1⟩, ⟨2, by simp, h2⟩, ⟨3, by simp, h3⟩,
      ⟨4, by simp, h4⟩, ⟨5, by simp, h5⟩, ⟨6, by simp, h6⟩]

/-- The sequence $P$ begins $23, 29, 59, 61, 67, 71, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_init :
    nth PillaiPrimes '' (Set.Icc 0 5) = {23, 29, 59, 61, 67, 71} := by
  have h := fun v hv => nth_count_eq_of_mem_iff (fun _ => mem_PillaiPrimes_of_lt) (v := v) hv
  have h0 : nth PillaiPrimes 0 = 23 := h 23 (by simp) (by norm_num)
  have h1 : nth PillaiPrimes 1 = 29 := h 29 (by simp) (by norm_num)
  have h2 : nth PillaiPrimes 2 = 59 := h 59 (by simp) (by norm_num)
  have h3 : nth PillaiPrimes 3 = 61 := h 61 (by simp) (by norm_num)
  have h4 : nth PillaiPrimes 4 = 67 := h 67 (by simp) (by norm_num)
  have h5 : nth PillaiPrimes 5 = 71 := h 71 (by simp) (by norm_num)
  ext x
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    interval_cases i <;> simp [h0, h1, h2, h3, h4, h5]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, by simp, h0⟩, ⟨1, by simp, h1⟩, ⟨2, by simp, h2⟩, ⟨3, by simp, h3⟩,
      ⟨4, by simp, h4⟩, ⟨5, by simp, h5⟩]

/-- Regarding the first question, Hardy and Subbarao computed all EHS numbers up to $2^{10}$, and
write "...if this trend conditions we expect [the limit] to be around 0.5, if it exists. The
frequency with which the EHS numbers occur - most often in long sequences of consecutive integers -
makes us believe that their asymptotic density exists and is unity. Erdős, though initially
hesitant, later agreed with this view." That is, the conjecture is that $S$ has density $1$. -/
@[category research open, AMS 11]
theorem erdos_1074.variants.EHSNumbers_one : EHSNumbers.HasDensity 1 := by
  sorry

end Erdos1074
