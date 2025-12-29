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
import FormalConjectures.ForMathlib.Topology.Algebra.InfiniteSum.Group
import FormalConjectures.ForMathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sequences with Large Gaps

*References:*
 - [Wa01] Wang, Yuefei. "On the Fatou set of an entire function with gaps." Tohoku Mathematical
    Journal, Second Series 53.1 (2001): 163-170.
-/

open Set Filter Topology
open scoped Finset

/-- A sequence of natural numbers `n₀ < n₁ < ...` is said to have Fabry gaps if `nₖ / k → ∞`.
This is the terminology adopted in [Wa01] and some other sources. -/
def HasFabryGaps (n : ℕ → ℕ) : Prop := StrictMono n ∧ Tendsto (fun k => n k / (k : ℝ)) atTop atTop

/-- A sequence of natural numbers `n₀ < n₁ < ...` is said to have Fejér gaps if `∑' 1 / nₖ < ∞`.
This is the terminology adopted in [Wa01] and some other sources. -/
def HasFejerGaps (n : ℕ → ℕ) : Prop := StrictMono n ∧ Summable (fun k => (n k : ℝ)⁻¹)

theorem HasFejerGaps.hasFabryGaps {f : ℕ → ℕ} (hf : HasFejerGaps f) : HasFabryGaps f := by
  refine ⟨hf.1, tendsto_atTop_mono'
    (f₁ := (· / 2) ∘ (·⁻¹) ∘ (∑' n : Set.Ici ·, (f n : ℝ)⁻¹) ∘ (· / 2)) _ ?_ <|
      (tendsto_div_const_atTop_of_pos (two_pos (α := ℝ))).2 <| tendsto_inv_nhdsGT_zero.comp <|
        .comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩) <| Nat.tendsto_div_const_atTop two_ne_zero⟩
  · filter_upwards [eventually_gt_atTop 1] with N hN
    simp only [Function.comp_apply, Nat.ofNat_pos, div_le_iff₀]
    have : 0 < f N := (hf.1 hN).bot_lt
    refine inv_le_of_inv_le₀ (by positivity) ?_
    calc
      (f N / N * 2 : ℝ)⁻¹
        = N / 2 * (f N : ℝ)⁻¹ := by grind
      _ ≤ #(.Ico (N / 2) N) • (f N : ℝ)⁻¹ := by simp; gcongr; simp [div_le_iff₀]; norm_cast; omega
      _ ≤ ∑ n ∈ .Ico (N / 2) N, (f n : ℝ)⁻¹ := Finset.card_nsmul_le_sum _ _ _ fun n hn ↦ by
        rw [Finset.mem_Ico] at hn
        have : 0 < f n := (hf.1 <| show 0 < n by omega).bot_lt
        grw [(hf.1 hn.2).le]
      _ ≤ ∑' n : Ici (N / 2), (f n : ℝ)⁻¹ :=
        hf.2.sum_le_tsum_set (by simp [Ico_subset_Ici_self]) (by simp)
  · exact hf.2.tendsto_tsum_zero (fun b ↦ by simpa using eventually_gt_atTop b)
  · filter_upwards [eventually_gt_atTop 1] with N hN
    refine (hf.2.comp_injective Subtype.val_injective).tsum_pos (by simp) ⟨N, by simp⟩ ?_
    simpa using (hf.1 hN).bot_lt
