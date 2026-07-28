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
# Erdős Problem 456

*References:*
- [erdosproblems.com/456](https://www.erdosproblems.com/456)
- [Er79e] Erdős, Paul, Some unconventional problems in number theory. Astérisque (1979), 73--82.
-/

open Nat Filter
open scoped Topology Classical Asymptotics

namespace Erdos456

/--
Let $p_n$ be the smallest prime $\equiv 1\pmod{n}$.
-/
noncomputable def p (n : ℕ) : ℕ :=
  sInf { k | k.Prime ∧ k ≡ 1 [MOD n] }

/--
Let $m_n$ be the smallest integer such that $n\mid \phi(m_n)$.
-/
noncomputable def m (n : ℕ) : ℕ :=
  sInf { k | 0 < k ∧ n ∣ totient k }

/--
Is it true that $m_n<p_n$ for almost all $n$?
-/
@[category research open, AMS 11]
theorem erdos_456.parts.i :
    answer(sorry) ↔
      Tendsto (fun N ↦ (count { n | m n < p n } N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  sorry

/--
Does $p_n/m_n \to \infty$ for almost all $n$?
-/
@[category research open, AMS 11]
theorem erdos_456.parts.ii :
    answer(sorry) ↔
      ∃ A : Set ℕ, Tendsto (fun N ↦ (count A N : ℝ) / (N : ℝ)) atTop (𝓝 1) ∧
        Tendsto (fun n ↦ (p n : ℝ) / (m n : ℝ)) (atTop ⊓ 𝓟 A) atTop := by
  sorry

/--
Are there infinitely many primes $p$ such that $p-1$ is the only $n$ for which $m_n=p$?
-/
@[category research open, AMS 11]
theorem erdos_456.parts.iii :
    answer(sorry) ↔
      { q | q.Prime ∧ ∀ n, m n = q ↔ n = q - 1 }.Infinite := by
  sorry

/--
Linnik's theorem implies that $p_n\leq n^{O(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_456.variants.linniks_theorem :
    ∃ L : ℝ, (fun n ↦ (p n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) ^ L) := by
  sorry

/--
It is trivial that $m_n \leq p_n$ always.
-/
@[category textbook, AMS 11]
theorem erdos_456.variants.mn_leq_pn (n : ℕ) :
    m n ≤ p n := by
  unfold m p
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hempty : {k | 0 < k ∧ (0 : ℕ) ∣ totient k} = (∅ : Set ℕ) := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hk
      rw [zero_dvd_iff]
      have := Nat.totient_pos.mpr hk
      omega
    rw [hempty, Nat.sInf_empty]
    exact Nat.zero_le _
  · have hne : {k | k.Prime ∧ k ≡ 1 [MOD n]}.Nonempty := by
      obtain ⟨q, _, hq, hmod⟩ :=
        Nat.forall_exists_prime_gt_and_modEq 0 hn (Nat.coprime_one_left n)
      exact ⟨q, hq, hmod⟩
    obtain ⟨hp, hmod⟩ := Nat.sInf_mem hne
    apply Nat.sInf_le
    refine ⟨hp.pos, ?_⟩
    rw [Nat.totient_prime hp]
    exact (Nat.modEq_iff_dvd' hp.pos).mp hmod.symm

/--
Erdős [Er79e] writes it is 'easy to show' that for infinitely many $n$ we have $m_n < p_n$.
-/
@[category research solved, AMS 11]
theorem erdos_456.variants.infinitely_many_n :
    { n | m n < p n }.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ ↦ 2 ^ (2 * j + 3))
  · intro a b hab
    apply Nat.pow_right_injective (by decide) at hab
    omega
  · intro j
    let k := 2 * j + 3
    -- Witness n = 2^k for odd k ≥ 3; then m(n) ≤ 2n, while 3 ∣ n + 1 forces p(n) > 2n.
    change m (2 ^ k) < p (2 ^ k)
    have hm : m (2 ^ k) ≤ 2 ^ (k + 1) := by
      unfold m
      refine Nat.sInf_le ⟨by positivity, ?_⟩
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      norm_num
    have hp : 2 ^ (k + 1) + 1 ≤ p (2 ^ k) := by
      unfold p
      let q := sInf {x | x.Prime ∧ x ≡ 1 [MOD 2 ^ k]}
      change 2 ^ (k + 1) + 1 ≤ q
      have hne : {x | x.Prime ∧ x ≡ 1 [MOD 2 ^ k]}.Nonempty := by
        obtain ⟨r, _, hr, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq 0
          (pow_ne_zero k (by decide)) (Nat.coprime_one_left (2 ^ k))
        exact ⟨r, hr, hmod⟩
      obtain ⟨hprime, hmod⟩ : q.Prime ∧ q ≡ 1 [MOD 2 ^ k] := Nat.sInf_mem hne
      rw [Nat.pow_succ]
      by_contra hbound
      have hxle : q ≤ 2 ^ k * 2 := by omega
      have hlower : 2 ^ k + 1 ≤ q := by
        simpa [add_comm] using hmod.symm.add_le_of_lt hprime.one_lt
      have hupper : q ≤ 2 ^ k + 1 :=
        (hmod.trans Nat.add_modEq_left.symm).le_of_lt_add (by omega)
      have hxeq : q = 2 ^ k + 1 := by omega
      have hkodd : Odd k := ⟨j + 1, by dsimp [k]; omega⟩
      have hxeqthree : q = 3 := (hprime.dvd_iff_eq (by decide)).mp (by
        rw [hxeq]
        simpa using hkodd.nat_add_dvd_pow_add_pow 2 1)
      have heighteen : 8 ≤ 2 ^ k := by
        change 2 ^ 3 ≤ 2 ^ k
        exact Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
      omega
    omega

/--
Erdős [Er79e] writes it is 'easy to show' that $m_n/n \to \infty$ for almost all $n$.
-/
@[category research solved, AMS 11]
theorem erdos_456.variants.m_div_n :
    ∃ A : Set ℕ, Tendsto (fun N ↦ (count A N : ℝ) / N) atTop (𝓝 1) ∧
      Tendsto (fun n ↦ (m n : ℝ) / (n : ℝ)) (atTop ⊓ 𝓟 A) atTop := by
  sorry

end Erdos456
