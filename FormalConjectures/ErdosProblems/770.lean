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
# Erdős Problem 770

*References:*
 - [erdosproblems.com/770](https://www.erdosproblems.com/770)
 - [Er49d] Erdös, P. "On the strong law of large numbers." Transactions of the American Mathematical
    Society 67.1 (1949): 51-56.
 - [Ma66] Matsuyama, Noboru. "On the strong law of large numbers." Tohoku Mathematical Journal,
    Second Series 18.3 (1966): 259-269.
-/

@[expose] public section

open Set ENat Filter

namespace Erdos770


/-- Let $h n$ be the minimal number such that $2 ^ n - 1, \dots, h(n) ^ n - 1$
are collectively coprime. -/
noncomputable def h (n : ℕ) : ℕ∞ := sInf {m | 2 < m ∧
  ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}

/-- If `1, …, M` are `n`-th roots of unity modulo a prime `q > M`, then `M ≤ n`. -/
@[category API, AMS 11]
lemma le_of_pow_eq_one {q n M : ℕ} [Fact q.Prime] (hn : 0 < n) (hM : M < q)
    (h : ∀ i ∈ Finset.Icc 1 M, (i : ZMod q) ^ n = 1) : M ≤ n := by
  classical
  have hinj : Set.InjOn (fun i : ℕ => (i : ZMod q)) (Finset.Icc 1 M : Finset ℕ) := by
    intro i hi j hj hij
    have hi' : i < q := by have := (Finset.mem_Icc.mp hi).2; omega
    have hj' : j < q := by have := (Finset.mem_Icc.mp hj).2; omega
    simpa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] using hij
  calc M = (Finset.Icc 1 M).card := by simp
    _ ≤ (Polynomial.nthRoots n (1 : ZMod q)).toFinset.card :=
        Finset.card_le_card_of_injOn _ (fun i hi => by
          simpa [Multiset.mem_toFinset, Polynomial.mem_nthRoots hn] using h i hi) hinj
    _ ≤ Multiset.card (Polynomial.nthRoots n (1 : ZMod q)) := Multiset.toFinset_card_le _
    _ ≤ n := Polynomial.card_nthRoots n 1

/-- A prime `q` divides the gcd of `i ^ n - 1` over `2 ≤ i ≤ m` iff each such `i` is an `n`-th
root of unity modulo `q`. -/
@[category API, AMS 11]
lemma prime_dvd_gcd_iff {q n m : ℕ} [Fact q.Prime] :
    q ∣ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id ↔ ∀ i ∈ Finset.Icc 2 m, (i : ZMod q) ^ n = 1 := by
  simp only [Finset.dvd_gcd_iff, Finset.forall_mem_image, id]
  refine forall₂_congr fun i hi => ?_
  have : 1 ≤ i ^ n := Nat.one_le_pow _ _ (by have := (Finset.mem_Icc.mp hi).1; omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub this, sub_eq_zero]
  simp

/-- A prime `q` dividing the gcd of `i ^ n - 1` over `2 ≤ i ≤ m` is larger than `m`, and each
`1 ≤ i ≤ m` is an `n`-th root of unity modulo `q`. -/
@[category API, AMS 11]
lemma lt_and_pow_eq_one {q n m : ℕ} [hq : Fact q.Prime] (hn : 0 < n)
    (h : q ∣ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id) :
    m < q ∧ ∀ i ∈ Finset.Icc 1 m, (i : ZMod q) ^ n = 1 := by
  rw [prime_dvd_gcd_iff] at h
  refine ⟨?_, fun i hi => ?_⟩
  · by_contra hle
    have := h q (Finset.mem_Icc.mpr ⟨hq.out.two_le, by omega⟩)
    simp [zero_pow hn.ne'] at this
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    rcases (by omega : i = 1 ∨ 2 ≤ i) with rfl | h2'
    · simp
    · exact h i (Finset.mem_Icc.mpr ⟨h2', h2⟩)

/-- `n + 1` is prime iff `h n = n + 1`. This is described as 'easy to see' in [Er74b]. -/
@[category textbook, AMS 11]
theorem Nat.Prime.h_eq_add_one {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime := by
  have hn0 : 0 < n := by omega
  constructor
  · intro hh
    by_contra hp
    obtain ⟨a, ⟨b, hab⟩, ha2, han⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hp
    have hb2 : 2 ≤ b := by
      by_contra hb; rw [not_le] at hb; nlinarith
    have hbn : b ≤ n := by nlinarith
    have hG : ((Finset.Icc 2 n).image fun i => (i ^ n - 1)).gcd id = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro q hq hdvd
      have := Fact.mk hq
      obtain ⟨hlt, hroots⟩ := lt_and_pow_eq_one hn0 hdvd
      have hlt' : n + 1 < q := lt_of_le_of_ne hlt fun h => hp (h ▸ hq)
      have := le_of_pow_eq_one hn0 hlt' fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
        rcases (by omega : i ≤ n ∨ i = n + 1) with h3 | rfl
        · exact hroots i (Finset.mem_Icc.mpr ⟨h1, h3⟩)
        · rw [hab, Nat.cast_mul, mul_pow, hroots a (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
            hroots b (Finset.mem_Icc.mpr ⟨by omega, hbn⟩), one_mul]
      omega
    have : h n ≤ n := sInf_le ⟨by exact_mod_cast hn, by simpa using hG⟩
    rw [hh] at this
    exact absurd this (by norm_cast; omega)
  · intro hp
    have := Fact.mk hp
    apply le_antisymm
    · refine sInf_le ⟨by exact_mod_cast (by omega : 2 < n + 1), ?_⟩
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro q hq hdvd
      have := Fact.mk hq
      rw [show ((n : ℕ∞) + 1).toNat = n + 1 from rfl] at hdvd
      obtain ⟨hlt, hroots⟩ := lt_and_pow_eq_one hn0 hdvd
      have := le_of_pow_eq_one hn0 hlt hroots
      omega
    · refine le_sInf fun m ⟨_, hm⟩ => ?_
      by_contra hlt
      rw [not_le] at hlt
      lift m to ℕ using ne_top_of_lt hlt
      have hmn : m < n + 1 := by exact_mod_cast hlt
      simp only [toNat_natCast] at hm
      have hdvd : n + 1 ∣ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id := by
        rw [prime_dvd_gcd_iff]
        intro i hi
        have hi0 : (i : ZMod (n + 1)) ≠ 0 := by
          obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
        simpa using ZMod.pow_card_sub_one_eq_one hi0
      rw [hm] at hdvd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)


/-- For odd `n`, the values of `h n` form an unbounded set.
This is described as 'easy to see' in [Er74b]. -/
@[category textbook, AMS 11]
theorem erdos_770.variants.odd_h_unbounded : Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd)):= by
  sorry


/-- For every prime `p`, does the density of integers with `h n = p` exist? -/
@[category research open, question, AMS 11]
theorem erdos_770.parts.i : ∀ p : ℕ, p.Prime → ∃ a, HasDensity {n | h n = p} a := by
  sorry

/-- Does `liminf h n = ∞`? -/
@[category research open, question, AMS 11]
theorem erdos_770.parts.ii : liminf h atTop = ⊤ := by
  sorry

/-- Is it true that if `p` is the greatest prime such that `p - 1 ∣ n` and `p > n ^ ε`, then
`h n = p`? -/
@[category research open, question, AMS 11]
theorem erdos_770.parts.iii : ∀ ε > 0, ∀ᶠ n in atTop,
    let p := sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}
    p > (n : ℝ) ^ (ε : ℝ) → h n = p := by
  sorry

/-- It is probably true that `h n = 3` for infinitely many `n`. -/
@[category research open, AMS 11]
theorem erdos_770.variants.three : {n | h n = 3}.Infinite := by
  sorry

end Erdos770
