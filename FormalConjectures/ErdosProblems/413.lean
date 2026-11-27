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
# Erdős Problem 413

*References:*
- [erdosproblems.com/413](https://www.erdosproblems.com/413)
- [A5236](https://oeis.org/A5236)
- [La26] Lau, C. F., *On the Number of Prime Factors of Consecutive Integers*.
  [arXiv:2604.15042](https://arxiv.org/abs/2604.15042) (2026).

Erdős called a natural number `n` a *barrier* for `ω`, the number of distinct prime divisors,
if `m + ω(m) ≤ n` for all `m < n`. He believed there should be infinitely many such barriers, and
even posed a relaxed variant asking whether there is some `ε > 0` for which infinitely many `n`
satisfy `m + ε · ω(m) ≤ n` for every `m < n`.
-/

@[expose] public section

open ArithmeticFunction
open scoped omega Omega

namespace Erdos413

/-- `IsBarrier f n` means `n` is a barrier for the real-valued function `f`,
i.e. `(m : ℝ) + f m ≤ (n : ℝ)` for all `m < n`. -/
def IsBarrier (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m < n, (m : ℝ) + f m ≤ n

/-- Are there infinitely many barriers for `ω`? -/
@[category research open, question, AMS 11]
theorem erdos_413.parts.i :
    { n | IsBarrier (fun m => ω m) n }.Infinite := by
  sorry

/-- `expProd n` is `∏ kᵢ` when `n = ∏ pᵢ ^ kᵢ`, i.e. the product of the prime exponents of `n`. -/
def expProd (n : ℕ) : ℕ :=
  n.factorization.prod fun _ e => e

/-- Erdős proved that the barrier set for `expProd` is infinite and even has positive density.

`HasPosDensity` is the right reading rather than positive lower density. In [Er79d] this is
Theorem 1, "the density of integers satisfying (2) is positive", where `d₀(n) = ∏ αᵢ` is
`expProd`. The averaging argument there bounds the density below, but Erdős states the existence
separately on the last page: "With a little more trouble, I can prove that the density of
integers `n` for which `n` is a barrier for `d₀(n)` exists." He goes further, that if `αᵢ` is the
density of `n` with `max_{m<n} (m + d₀(m)) = n + i`, then every `αᵢ` exists and they sum to `1`.

[Er79d] Erdős, P., *Some unconventional problems in number theory*.
Acta Math. Acad. Sci. Hungar. (1979), 71-80. -/
@[category research solved, AMS 11]
theorem erdos_413.variants.hasPosDensity_barrier_expProd :
    { n | IsBarrier (fun m => expProd m) n }.HasPosDensity := by
  sorry

/-- Erdős believed there should be infinitely many barriers for `Ω`, the total prime multiplicity. -/
@[category research open, question, AMS 11]
theorem erdos_413.variants.bigOmega :
    { n | IsBarrier (fun m => Ω m) n }.Infinite := by
  sorry

/-- `2 ^ Ω m ≤ m` for `m ≠ 0`: each prime factor is at least `2`. -/
@[category API, AMS 11]
theorem two_pow_bigOmega_le {m : ℕ} (hm : m ≠ 0) : 2 ^ Ω m ≤ m := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc 2 ^ m.primeFactorsList.length ≤ m.primeFactorsList.prod :=
        List.pow_card_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
    _ = m := Nat.prod_primeFactorsList hm

/-- Selfridge computed that the largest `Ω`-barrier below `10^5` is `99840`.

Proof idea: `2 ^ Ω m ≤ m` bounds `Ω` below `99840`; the rest is explicit evaluation of `Ω`. -/
@[category research solved, AMS 11]
theorem erdos_413.variants.bigOmega_largest_barrier_lt_100k :
    IsGreatest {n : ℕ | n < 10 ^ 5 ∧ IsBarrier (fun m => Ω m) n} 99840 := by
  constructor
  · refine ⟨by norm_num, fun m hm => ?_⟩
    show (m : ℝ) + (Ω m : ℝ) ≤ 99840
    by_cases h : m < 99824
    · have h2 : Ω m ≤ 16 := by
        by_contra hc
        have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_le.1 hc)
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hc
        · have := two_pow_bigOmega_le hpos.ne'
          omega
      have h3 : (Ω m : ℝ) ≤ 16 := by exact_mod_cast h2
      have h4 : (m : ℝ) ≤ 99823 := by exact_mod_cast (by omega : m ≤ 99823)
      linarith
    · push Not at h
      have h3 : m + Ω m ≤ 99840 := by
        interval_cases m <;>
          simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]
      exact_mod_cast h3
  · rintro n ⟨hn, hb⟩
    by_contra hlt
    push Not at hlt
    -- pairs `(m, Ω m)` whose `m + Ω m` rules out every barrier in `(99840, 10^5)`
    set L : List (ℕ × ℕ) := [
        (99840, 12), (99848, 5), (99852, 5), (99856, 6), (99860, 4), (99862, 4), (99864, 7),
        (99870, 4), (99873, 7), (99876, 6), (99880, 6), (99885, 3), (99887, 2), (99888, 6),
        (99892, 5), (99896, 4), (99897, 4), (99900, 8), (99904, 8), (99909, 4), (99912, 6),
        (99916, 3), (99918, 6), (99920, 6), (99924, 5), (99928, 4), (99930, 4), (99932, 5),
        (99936, 8), (99940, 5), (99944, 6), (99946, 5), (99950, 4), (99952, 5), (99954, 6),
        (99957, 4), (99960, 8), (99966, 3), (99968, 9), (99975, 5), (99978, 4), (99981, 6),
        (99984, 6), (99988, 4), (99990, 6), (99992, 5), (99996, 5)] with hL
    have hΩ : ∀ p ∈ L, Ω p.1 = p.2 := by
      simp [hL, ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]
    have key : ∀ p ∈ L, p.1 < n → p.1 + p.2 ≤ n := fun p hp h => by
      have h5 : (p.1 : ℝ) + (Ω p.1 : ℝ) ≤ n := hb p.1 h
      rw [hΩ p hp] at h5
      exact_mod_cast h5
    simp only [hL, List.mem_cons, forall_eq_or_imp, List.not_mem_nil, false_imp_iff,
      implies_true, and_true] at key
    omega

/-- Does there exist some $\epsilon > 0$ such that there are infinitely many
$\epsilon$-barriers for $\omega$? Lau [La26, Theorem 1.3] gives a positive answer. -/
@[category research solved, question, AMS 11]
theorem erdos_413.parts.ii :
    (∃ ε > (0 : ℝ), { n | IsBarrier (fun n => ε * ω n) n }.Infinite) := by
  sorry

end Erdos413
