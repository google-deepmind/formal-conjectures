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
# Conjectures about the Mandelbrot and Multibrot sets
This file adds three conjectures about the Mandelbrot and Multibrot sets:
- the *MLC conjecture*, stating that these sets are locally connected
- the *density of hyperbolicity* conjecture, stating that parameters with attracting cycles are
  dense in the Mandelbrot and Multibrot sets
- the conjecture that the boundaries of these sets have zero area.
The first two conjectures are related in that the former implies the latter.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity)
 - [arxiv/math/9902155](https://arxiv.org/abs/math/9902155)
 - [mathoverflow/37229](https://mathoverflow.net/questions/37229/)
-/

open Topology Set Function Filter Bornology Metric MeasureTheory

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrot set for n = 2. In other words, it is the
set of all parameters `c : ℂ` for which `0` does not escape to infinity under repeated application
of `z ↦ z ^ 2 + c`. -/
abbrev mandelbrotSet := multibrotSet 2

/-- The `multibrotSet n` is equivalently the set of all parameters `c` for which the orbit of `0`
under `z ↦ z ^ n + c` does not leave the closed disk of radius `2 ^ (n - 1)⁻¹` around the origin. -/
@[category API, AMS 37]
theorem multibrotSet_eq {n : ℕ} (hn : 2 ≤ n) :
    multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹} := by
  replace hn := one_lt_two.trans_le hn
  set r : ℝ := 2 ^ (n - 1 : ℝ)⁻¹
  have hr : 0 < r := by positivity
  have hr' : r ^ (n - 1) = 2 := by
    simp [r, ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le, hn.le,
      show (n - 1 : ℝ) ≠ 0 by simpa [sub_ne_zero] using hn.ne.symm]
  have hr'' : r ^ n = 2 * r := by simp [← hr', ← pow_succ, hn.le]
  ext c; refine ⟨fun h k ↦ ?_, fun h h' ↦ ?_⟩ <;> dsimp [mandelbrotSet, multibrotSet] at h ⊢
  · refine of_not_not fun h' ↦ h ?_
    replace ⟨k, h, h'⟩ :
        ∃ k, r < ‖(fun z ↦ z ^ n + c)^[k] 0‖ ∧ ‖c‖ ≤ ‖(fun z ↦ z ^ n + c)^[k] 0‖ := by
      refine (le_or_lt ‖c‖ r).elim (fun h ↦ ⟨k, ?_, ?_⟩) fun h ↦ ⟨1, by
        simp [h, zero_pow (M₀ := ℂ) (one_pos.trans hn).ne.symm]⟩ <;> linarith
    let a := ‖(fun z ↦ z ^ n + c)^[k] 0‖ - r
    have ha : 0 < a := by unfold a; linarith
    have h' m : r + a * n ^ m ≤ ‖(fun z ↦ z ^ n + c)^[k + m] 0‖ := by
      induction' m with m hm
      · simp [a]
      · rw [← add_assoc, iterate_succ_apply']
        refine .trans ?_ <| norm_sub_le_norm_add _ _
        replace hm :
            r ^ n + a * n ^ m * r ^ (n - 1) * ↑n ≤ ‖(fun z ↦ z ^ n + c)^[k + m] 0‖ ^ n := by
          refine .trans ?_ (pow_le_pow_left₀ (by positivity) hm n); cases n; simp
          rw [add_comm r _, add_pow]
          refine .trans ?_ <| Finset.add_le_sum (by intros; positivity) ?_ ?_ zero_ne_one <;> simp
        rw [norm_pow, pow_succ]
        refine .trans ?_ (sub_le_sub hm h')
        rw [hr', hr'', show ‖(fun z ↦ z ^ n + c)^[k] 0‖ = a + r by simp [a]]
        suffices a ≤ a * (n * n ^ m) by linarith
        refine (mul_one a).symm.trans_le <| (mul_le_mul_left ha).2 ?_
        have hn : 1 ≤ (n : ℝ) := Nat.one_le_cast.2 hn.le
        simpa using mul_le_mul hn (one_le_pow₀ hn)
    rw [← tendsto_norm_atTop_iff_cobounded]
    suffices h' : Tendsto (fun m ↦ ‖(fun z ↦ z ^ n + c)^[k + m] 0‖) atTop atTop by
      rw [tendsto_atTop_atTop] at h' ⊢
      intro x; let ⟨l, h'⟩ := h' x
      refine ⟨k + l, fun m hm ↦ ?_⟩
      specialize h' (m - k) (Nat.le_sub_of_add_le' hm)
      rwa [Nat.add_sub_cancel' <| (Nat.le_add_right _ _).trans hm] at h'
    exact tendsto_atTop_mono h' <| tendsto_atTop_add_const_left _ _ <| .const_mul_atTop ha <|
      tendsto_pow_atTop_atTop_of_one_lt <| Nat.one_lt_cast.2 hn
  · specialize h' (isBounded_closedBall (x := 0) (r := r))
    rw [mem_map, mem_atTop_sets] at h'; replace ⟨n, h'⟩ := h'
    exact not_lt_of_le (h n) (by simpa using h' n)

/-- The mandelbrot set is equivalently the set of all parameters `c` for which the orbit of `0`
under `z ↦ z ^ 2 + c` does not leave the closed disk of radius two around the origin. -/
@[category API, AMS 37]
theorem mandelbrotSet_eq : mandelbrotSet = {c | ∀ k, ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by
  simpa [show (2 - 1 : ℝ) = 1 by norm_num] using multibrotSet_eq le_rfl

/-- The MLC conjecture, stating that the mandelbrot set is locally connected. -/
@[category research open, AMS 37]
theorem MLC : LocallyConnectedSpace mandelbrotSet := by
  sorry

/-- A stronger version of the MLC conjecture, stating that all multibrots are locally connected.
Note that we don't need to require `2 ≤ n` because the conjecture holds in the trivial cases `n = 0`
and `n = 1` too. -/
@[category research open, AMS 37]
theorem MLC_general_exponent (n : ℕ) : LocallyConnectedSpace (multibrotSet n) := by
  sorry

/-- We say that `z : ℂ` is part of an attracting cycle of period `n` of `f : ℂ → ℂ` if it is an
`n`-periodic point (i.e. `f^[n] z = z`), `f^[n]` is differentiable at `z` and `‖deriv f^[n] z‖` is
strictly less than one.-/
def IsAttractingCycle (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Prop :=
  f.IsPeriodicPt n z ∧ DifferentiableAt ℂ f^[n] z ∧ ‖deriv f^[n] z‖ < 1

/-- For example, `0` is part of an attracting `2`-cycle of `z ↦ z ^ 2 - 1`. -/
@[category test, AMS 37]
example : IsAttractingCycle (fun z ↦ z ^ 2 - 1) 2 0 :=
  ⟨by simp [IsPeriodicPt, IsFixedPt], by fun_prop, by simp [deriv_comp]⟩

/-- On the other hand, while `2` is part of a `1`-cycle of `z ↦ z ^ 2 - 2`, that cycle is not
attracting. -/
@[category test, AMS 37]
example : ¬ IsAttractingCycle (fun z ↦ z ^ 2 - 2) 1 2 := by
  simp [IsAttractingCycle, show (1 : ℝ) ≤ 2 * 2 by norm_num]

/-- No function has an attracting cycle of period `0`. This is important in that it means we don't
need to require `0 < n` in the conjectures below. -/
@[category test, AMS 37]
example (f : ℂ → ℂ) (z : ℂ) : ¬ IsAttractingCycle f 0 z := by
  simp [IsAttractingCycle]

/-- The density of hyperbolicity conjecture, stating that the set of all parameters `c` for which
`fun z ↦ z ^ 2 + c` has an attracting cycle is dense in the Mandelbrot set. -/
@[category research open, AMS 37]
theorem density_of_hyperbolicity :
    mandelbrotSet ⊆ closure {c | ∃ n z, IsAttractingCycle (fun z ↦ z ^ 2 + c) n z} := by
  sorry

/-- The density of hyperbolicity conjecture for Multibrot sets, stating that the set of all
parameters `c` for which `fun z ↦ z ^ n + c` has an attracting cycle is dense in `multibrotSet n`.
Note that we need to require `2 ≤ n` because the conjecture is trivially false for `n = 1`. -/
@[category research open, AMS 37]
theorem density_of_hyperbolicity_general_exponent {n : ℕ} (hn : 2 ≤ n) :
    multibrotSet n ⊆ closure {c | ∃ n z, IsAttractingCycle (fun z ↦ z ^ n + c) n z} := by
  sorry

/-- The boundary of any Multibrot set is measurable because it is closed, so it makes sense to
ask about its area. -/
@[category test, AMS 37]
example {n : ℕ} : MeasurableSet (frontier (multibrotSet n)) := isClosed_frontier.measurableSet

/-- The boundary of the Mandelbrot set is conjectured to have zero area. -/
@[category research open, AMS 37]
theorem volume_frontier_mandelbrotSet_eq_zero : volume (frontier mandelbrotSet) = 0 := by
  sorry

/-- The boundary of any Multibrot set is conjectured to have zero area.
Note that we don't need to exclude the trivial cases `n = 0` and `n = 1` because the conjecture
holds for them. -/
@[category research open, AMS 37]
theorem volume_frontier_multibrotSet_eq_zero {n : ℕ} : volume (frontier (multibrotSet n)) = 0 := by
  sorry
