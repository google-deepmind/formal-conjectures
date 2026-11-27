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
import FormalConjectures.Millennium.RiemannHypothesis
import FormalConjectures.Wikipedia.CramerConjecture

/-!
# Erdős Problem 462

*References:*
- [Erdős Problem 462](https://www.erdosproblems.com/462)
- A. Dudek, L. Grenié, and G. Molteni, [Primes in explicit short intervals on RH](
  https://arxiv.org/abs/1503.05403).
-/

@[expose] public section

namespace Erdos462

open Filter
open scoped BigOperators

/--
Let $p(n)$ denote the least prime factor of $n$. Is there a constant $C>0$ such that
$$\sum_{x\leq n\leq x+C\sqrt{x}(\log x)^2}\frac{p(n)}{n}\gg 1$$
for all sufficiently large $x$?

With primes included in the sum, the answer is yes with $C=c=1$. Cramér's bound on prime
gaps under RH supplies a prime in the interval for all sufficiently large $x$.
-/
@[category research solved, question, AMS 11]
theorem erdos_462 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c ≤ ∑ n ∈ Finset.Icc x
        ⌊(x : ℝ) + C * Real.sqrt x * (Real.log x) ^ 2⌋₊, (n.minFac : ℝ) / n := by
  have hgap := CramerConjecture.cramer_conjecture.variants.conditional_rh
    RiemannHypothesis.riemannHypothesis
  obtain ⟨K, hK, hb⟩ := hgap.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hb.bound
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  filter_upwards [Nat.tendsto_primeCounting'.eventually_ge_atTop (N + 1),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K]
    with x hx hlog
  change K ≤ Real.log (x : ℝ) at hlog
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show x.primeCounting' ≠ 0 by omega)
  let p := Nat.nth Nat.Prime k
  let q := Nat.nth Nat.Prime (k + 1)
  have hpx : p < x := Nat.nth_lt_of_lt_count (p := Nat.Prime) (by
    change k < x.primeCounting'
    omega)
  have hxq : x ≤ q := by
    change x ≤ Nat.nth Nat.Prime k.succ
    rw [← hk]
    exact Nat.le_nth_count Nat.infinite_setOfPred_prime x
  have hp : p.Prime := Nat.prime_nth_prime _
  have hq : q.Prime := Nat.prime_nth_prime _
  have hpx' : (p : ℝ) ≤ x := by exact_mod_cast hpx.le
  have hlogp := Real.log_nonneg (show 1 ≤ (p : ℝ) by exact_mod_cast hp.one_le)
  have h := hN k (by omega)
  change ‖((q - p : ℕ) : ℝ)‖ ≤ K * ‖Real.sqrt p * Real.log p‖ at h
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_sub (hpx.le.trans hxq),
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlogp)] at h
  have hmono := mul_le_mul (Real.sqrt_le_sqrt hpx')
    (Real.log_le_log (by exact_mod_cast hp.pos) hpx') hlogp (Real.sqrt_nonneg _)
  have hwidth := mul_le_mul_of_nonneg_left hmono hK.le
  have hlarge := mul_le_mul_of_nonneg_right hlog
    (mul_nonneg (Real.sqrt_nonneg (x : ℝ)) (hK.le.trans hlog))
  have hmem : q ∈ Finset.Icc x ⌊(x : ℝ) + 1 * Real.sqrt x * (Real.log x) ^ 2⌋₊ :=
    Finset.mem_Icc.mpr ⟨hxq, Nat.le_floor (by linarith)⟩
  calc
    (1 : ℝ) = (q.minFac : ℝ) / q := by simp [hq.minFac_eq, hq.ne_zero]
    _ ≤ _ := Finset.single_le_sum (f := fun n : ℕ => (n.minFac : ℝ) / n)
      (fun _ _ => by positivity) hmem

end Erdos462
