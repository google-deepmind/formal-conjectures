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
# Erdős Problem 158

*References:*
 - [erdosproblems.com/158](https://www.erdosproblems.com/158)
 - [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
    Theory (1994), 329-347.
-/

open Cardinal Filter ENNReal

/-- A set `A ⊆ ℕ` is said to be a `B₂[g]` set if for all `n`, the equation
`a + a' = n, a ≤ a', a, a' ∈ A` has at most `g` solutions. This is defined in [ESS94]. -/
def B2 (g : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, #{x : ℕ × ℕ | x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A} ≤ g

/-- A Sidon set is `B₂[1]`. -/
@[category API, AMS 5]
lemma IsSidon.B2 (A : Set ℕ) (hA : IsSidon A) : B2 1 A := by
  refine fun n => le_one_iff_subsingleton.2 (subsingleton_iff.2 fun ⟨x, h, p, q⟩ ⟨y, r, s, t⟩ => ?_)
  have := hA x.1 q.1 y.1 t.1 x.2 q.2 y.2 t.2 (h.trans r.symm)
  grind

namespace Erdos158

/-- Let `A` be an infinite `B₂[2]` set. Must `liminf |A ∩ {1, ..., N}|/√N = 0`? -/
@[category research open, AMS 5]
theorem erdos_158.B22 : answer(sorry) ↔ ∀ A : Set ℕ, A.Infinite → B2 2 A →
    liminf (fun N : ℕ => (A ∩ (Finset.range N)).ncard / √N) atTop = 0 := by
  sorry

/-- Let `A` be an infinite Sidon set. Then `liminf |A ∩ {1, ..., N}| * (log N / N) ^ (1 / 2) < ∞`.
This is proved in [ESS94]. -/
@[category research solved, AMS 5]
theorem erdos_158.isSidon' {A : Set ℕ} (hp : A.Infinite) (hq : IsSidon A) :
    liminf (fun N : ℕ => (A ∩ (Finset.range N)).ncard * ENNReal.ofReal (√(Real.log N / N)))
    atTop < ⊤ := by
  sorry

/-- As a corollary of `erdos_158.isSidon'`, we can prove that `liminf |A ∩ {1, ..., N}|/√N = 0` for
any infinite Sidon set `A`. -/
@[category research solved, AMS 5]
theorem erdos_158.isSidon {A : Set ℕ} (hp : A.Infinite) (hq : IsSidon A) :
    liminf (fun N : ℕ => (A ∩ (Finset.range N)).ncard / √(N : ℝ)) atTop = 0 := by
  have := erdos_158.isSidon' hp hq
  contrapose! this with h
  have hg : Tendsto (fun N => (A ∩ (Finset.range N)).ncard * √(Real.log N / N)) atTop atTop := by
    have hl : Tendsto (fun N => (A ∩ (Finset.range N)).ncard / √N * √(Real.log N)) atTop atTop := by
      obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∀ᶠ N in atTop, (A ∩ (Finset.range N)).ncard / √N ≥ c := by
        simp only [liminf_eq, eventually_atTop, ne_eq] at h
        by_cases h_zero : ∀ a ∈ {a : ℝ | ∃ a_1 : ℕ, ∀ N : ℕ, a_1 ≤ N → a ≤ (A ∩ (Finset.range N)).ncard / √N}, a ≤ 0
        · exact False.elim <| h <| le_antisymm ( csSup_le ⟨ 0, ⟨ 0, fun n hn => by positivity ⟩ ⟩ h_zero ) <| le_csSup ⟨ 0, h_zero ⟩ ⟨ 0, fun n hn => by positivity ⟩;
        · aesop;
      refine' tendsto_atTop_mono' _ _ _
      exacts [ fun N => c * Real.sqrt ( Real.log N ), by filter_upwards [ hc, Filter.eventually_gt_atTop 1 ] with N hN₁ hN₂ using mul_le_mul_of_nonneg_right hN₁ <| Real.sqrt_nonneg _, Filter.Tendsto.const_mul_atTop hc_pos <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ ⌈Real.exp ( x ^ 2 ) ⌉₊ + 1, fun N hN => Real.le_sqrt_of_sq_le <| Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| by linarith [ Nat.le_ceil ( Real.exp ( x ^ 2 ) ), show ( N : ℝ ) ≥ ⌈Real.exp ( x ^ 2 ) ⌉₊ + 1 by exact_mod_cast hN ] ⟩ ]
    convert hl using 1
    norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [Tendsto.liminf_eq]
  simpa [ofReal_mul, Function.comp_def] using tendsto_ofReal_atTop.comp hg

end Erdos158
