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
# Erdős Problem 517

*Reference:*
 - [erdosproblems.com/517](https://www.erdosproblems.com/517)
 - [Bi28] Biernacki, Miécislas, Sur les équations algébriques contenant des paramétres arbitraires.
    (1928), 145.
 - [Wa01] Wang, Yuefei. "On the Fatou set of an entire function with gaps." Tohoku Mathematical
    Journal, Second Series 53.1 (2001): 163-170.
-/

open Set Filter Topology

/-- A sequence of natural numbers `n₀ < n₁ < ...` is said to have Fabry gaps if `nₖ / k → ∞`.
This is the terminology adopted in [Wa01] and some other sources. -/
def HasFabryGaps (n : ℕ → ℕ) : Prop := StrictMono n ∧ Tendsto (fun k => n k / (k : ℝ)) atTop atTop

/-- A sequence of natural numbers `n₀ < n₁ < ...` is said to have Fejér gaps if `∑' 1 / nₖ < ∞`.
This is the terminology adopted in [Wa01] and some other sources. -/
def HasFejerGaps (n : ℕ → ℕ) : Prop := StrictMono n ∧ Summable (fun k => 1 / (n k : ℝ))

@[category API, AMS 40]
theorem HasFejerGaps.HasFabryGaps {n : ℕ → ℕ} (hn : HasFejerGaps n) : HasFabryGaps n := by
  refine ⟨hn.1, tendsto_atTop_atTop.2 fun b => ?_⟩
  by_cases hb : b > 0
  · have : Ico (-1 / (2 * b)) (1 / (2 * b)) ∈ (𝓝 0) := by
      simp_all only [gt_iff_lt, one_div, mul_inv_rev, Ico_mem_nhds_iff, mem_Ioo, inv_pos,
        mul_pos_iff_of_pos_left, Nat.ofNat_pos, and_true]
      exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    /- Choose `k` large enough so that the tail sum is small. -/
    obtain ⟨k, hk⟩ := hn.2.nat_tsum_vanishing this
    refine ⟨2 * k + 2, fun m hm => ?_⟩
    suffices m / n m ≤ 1 / b from by
      refine (le_div_comm₀ hb (by norm_cast; linarith)).2 ?_
      have hnm : 0 < n m := (hn.1.imp (by linarith : 0 < m)).trans_le' (by linarith)
      simpa using (div_le_iff₀' (by norm_cast)).1 this
    calc
    _ ≤ 2 * (m / 2 / (n m : ℝ)) := by ring_nf; rfl
    _ ≤ 2 * ∑ j : Ico (m / 2) m, 1 / (n m : ℝ) := by
      gcongr
      simp only [div_eq_mul_inv ((m : ℝ) / 2), one_div, Finset.sum_const, Finset.card_univ,
        Fintype.card_ofFinset, Nat.card_Ico, nsmul_eq_mul]
      gcongr
      simp only [Nat.cast_sub (by omega : m / 2 ≤ m)]
      rw (config := {occs := .neg [1]}) [← add_halves (m : ℝ)]
      exact le_sub_right_of_add_le (add_le_add_left Nat.cast_div_le (m / 2 : ℝ))
    _ ≤ 2 * ∑ j : Ico (m / 2) m, 1 / (n j : ℝ) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i a ↦
        one_div_le_one_div_of_le ?_ ?_) (by linarith)
      · norm_cast
        refine (hn.1.imp (LT.lt.trans_le ?_ i.2.1)).trans_le' (by linarith : 0 ≤ n 0)
        simp; linarith
      · exact_mod_cast hn.1.monotone i.2.2.le
    _ ≤ 2 * (1 / (2 * b)) := by
      gcongr
      have : Ico (m / 2) m ⊆ {n | k ≤ n} := by
        refine fun x hx => LE.le.trans ?_ hx.1
        simp [Nat.le_div_two_iff_mul_two_le]
        linarith
      simpa [tsum_fintype] using (hk (Ico (m / 2) m) this).2.le
    _ = 1 / b := by grind
  · exact ⟨0, fun m hm => (not_lt.1 hb).trans (div_nonneg (by linarith) (by linarith))⟩

namespace Erdos517

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `nₖ / k → ∞`, is it true that `f` assumes
every value infinitely often? -/
@[category research open, AMS 30]
theorem erdos_517.fabry : answer(sorry) ↔ ∀ {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : HasFabryGaps n)
    {a : ℕ → ℂ} (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (z : ℂ),
    {x : ℂ | f x = z}.Infinite := by
  sorry

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `∑ 1 / nₖ < ∞`, then `f` assumes every value
infinitely often. This theorem is proved in [Bi28]. -/
@[category research solved, AMS 30]
theorem erdos_517.fejer {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : HasFejerGaps n) {a : ℕ → ℂ}
    (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (z : ℂ) : {x : ℂ | f x = z}.Infinite :=
  sorry

end Erdos517
