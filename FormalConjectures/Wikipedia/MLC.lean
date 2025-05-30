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
# Local connectivity of the Mandelbrot and Multibrot sets

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity)
-/

open Topology Set Function Filter Bornology Metric

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrot set for n = 2. In other words, it is the
set of all parameters `c : ℂ` for which `0` does not escape to infinity under repeated application
of `z ↦ z ^ 2 + c`. -/
abbrev mandelbrotSet := multibrotSet 2

/- To test the definition, we show that the mandelbrot set is equivalently the set of all parameters
`c` for which the orbit of `0` under `z ↦ z ^ 2 + c` does not leave the closed disk of radius two
around the origin. -/
@[category test]
example : mandelbrotSet = {c | ∀ k, ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by
  ext c; refine ⟨fun h k ↦ ?_, fun h h' ↦ ?_⟩ <;> dsimp [mandelbrotSet, multibrotSet] at h ⊢
  · refine of_not_not fun h' ↦ h ?_
    replace ⟨k, h, h'⟩ :
        ∃ k, 2 < ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ∧ ‖c‖ ≤ ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ := by
      refine (le_or_lt ‖c‖ 2).elim (fun h ↦ ⟨k, ?_, ?_⟩) fun h ↦ ⟨1, by simp [h]⟩ <;> linarith
    let a := ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ - 2
    have ha : 0 < a := by unfold a; linarith
    have h' m : 2 + a * 2 ^ m ≤ ‖(fun z ↦ z ^ 2 + c)^[k + m] 0‖ := by
      induction' m with m hm
      · simp [a]
      · rw [← add_assoc, iterate_succ_apply']
        refine .trans ?_ <| norm_sub_le_norm_add _ _
        replace hm := pow_le_pow_left₀ (by positivity) hm 2
        rw [add_sq] at hm; rw [norm_pow, pow_succ]
        refine .trans ?_ (sub_le_sub hm h')
        have : a ≤ a * (2 * (2 : ℝ) ^ m) := by
          refine (mul_one a).symm.trans_le <| (mul_le_mul_left ha).2 ?_
          linarith [one_le_pow₀ (M₀ := ℝ) one_lt_two.le (n := m)]
        rw [show ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ = a + 2 by simp [a]]
        linarith [show 0 < (a * 2 ^ m) ^ 2 by positivity]
    rw [← tendsto_norm_atTop_iff_cobounded]
    suffices h' : Tendsto (fun m ↦ ‖(fun z ↦ z ^ 2 + c)^[k + m] 0‖) atTop atTop by
      rw [tendsto_atTop_atTop] at h' ⊢
      intro x; let ⟨l, h'⟩ := h' x
      refine ⟨k + l, fun m hm ↦ ?_⟩
      specialize h' (m - k) (Nat.le_sub_of_add_le' hm)
      rwa [Nat.add_sub_cancel' <| (Nat.le_add_right _ _).trans hm] at h'
    exact tendsto_atTop_mono h' <| tendsto_atTop_add_const_left _ _ <| .const_mul_atTop ha <|
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  · specialize h' (isBounded_closedBall (x := 0) (r := 2))
    rw [mem_map, mem_atTop_sets] at h'; replace ⟨n, h'⟩ := h'
    exact not_lt_of_le (h n) (by simpa using h' n)

/-- The MLC conjecture, stating that the mandelbrot set is locally connected. -/
@[category research open, AMS 37]
theorem MLC : LocallyConnectedSpace mandelbrotSet := by
  sorry

/-- A stronger version of the MLC conjecture, stating that all multibrots are locally connected.
Note that we don't need to require `2 ≤ n` because the conjecture holds in the trivial cases `n = 0`
and `n = 1` too. -/
@[category research open, AMS 37]
theorem MLC' n : LocallyConnectedSpace (multibrotSet n) := by
  sorry
