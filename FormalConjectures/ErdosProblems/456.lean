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

import FormalConjectures.Util.ProblemImports

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
  rcases eq_or_ne n 0 with rfl | hn
  · -- When `n = 0` the set defining `m 0` is empty (no `k > 0` has `φ k = 0`), so `m 0 = 0`.
    have hm0 : m 0 = 0 := by
      simp only [m, Nat.sInf_eq_zero]
      right
      rw [Set.eq_empty_iff_forall_notMem]
      rintro k ⟨hk, hdvd⟩
      rw [zero_dvd_iff, Nat.totient_eq_zero] at hdvd
      omega
    simp [hm0]
  · -- For `n ≠ 0` Dirichlet gives a prime `≡ 1 [MOD n]`, so `p n` realises the infimum and is
    -- itself a prime `≡ 1 [MOD n]`.  Then `n ∣ φ(p n) = p n - 1`, so `p n` lies in the set
    -- defining `m n`, whence `m n ≤ p n`.
    have hne : {k | k.Prime ∧ k ≡ 1 [MOD n]}.Nonempty := by
      obtain ⟨q, hq, _, hmod⟩ := Nat.exists_prime_gt_modEq_one 0 hn
      exact ⟨q, hq, hmod⟩
    obtain ⟨hprime, hmod⟩ := Nat.sInf_mem hne
    simp only [m, p]
    apply Nat.sInf_le
    refine ⟨hprime.pos, ?_⟩
    rw [Nat.totient_prime hprime]
    exact (Nat.modEq_iff_dvd' hprime.one_lt.le).mp hmod.symm

/--
Erdős [Er79e] writes it is 'easy to show' that for infinitely many $n$ we have $m_n < p_n$.
-/
@[category research solved, AMS 11]
theorem erdos_456.variants.infinitely_many_n :
    { n | m n < p n }.Infinite := by
  sorry

/--
Erdős [Er79e] writes it is 'easy to show' that $m_n/n \to \infty$ for almost all $n$.
-/
@[category research solved, AMS 11]
theorem erdos_456.variants.m_div_n :
    ∃ A : Set ℕ, Tendsto (fun N ↦ (count A N : ℝ) / N) atTop (𝓝 1) ∧
      Tendsto (fun n ↦ (m n : ℝ) / (n : ℝ)) (atTop ⊓ 𝓟 A) atTop := by
  sorry

end Erdos456
