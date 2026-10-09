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

import Mathlib

/-!
# The theta tail beyond three terms

`θ(t) − 1 = Σ_{n ≥ 1} 2 e^{−π n² t}` (`hasSum_nat_cosKernel₀` at `a = 0`), and for `t ≥ 1`

  `0 ≤ θ(t) − 1 − Σ_{n=1}^{3} 2 e^{−π n² t} ≤ 4 e^{−16 π t}`,

since `(m+4)² ≥ 16 + m` and `e^{−π t} ≤ e^{−π} ≤ 1/2`.  This lets the Mellin integral of
`A = 1_{x>1}(θ − 1)` be replaced by three explicit exponentials plus a `≤ 4 e^{−16π}/(16π)` error.
AUTHORITY_EFFECT = NONE.
-/

open Real HurwitzZeta

namespace AEGIS.RHThetaTailV1

/-- `θ(t) − 1 = Σ_{n≥0} 2 e^{−π (n+1)² t}`. -/
theorem theta_sub_one_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => 2 * rexp (-π * (n + 1) ^ 2 * t)) (evenKernel 0 t - 1) := by
  have h := hasSum_nat_cosKernel₀ 0 ht
  rw [QuotientAddGroup.mk_zero, ← evenKernel_eq_cosKernel_of_zero] at h
  simpa using h

lemma exp_neg_pi_le_half : rexp (-π) ≤ 1 / 2 := by
  have h1 : 1 + π ≤ rexp π := by linarith [Real.add_one_le_exp π]
  have h2 : (2 : ℝ) ≤ rexp π := by linarith [Real.pi_gt_three]
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h2

lemma term_le {t : ℝ} (ht : 1 ≤ t) (n : ℕ) :
    2 * rexp (-π * (((n + 3 : ℕ) : ℝ) + 1) ^ 2 * t) ≤ 2 * rexp (-16 * π * t) * (1 / 2) ^ n := by
  have hpi := Real.pi_pos
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hsq : (16 : ℝ) + n ≤ (((n + 3 : ℕ) : ℝ) + 1) ^ 2 := by push_cast; nlinarith
  have e1 : rexp (-π * (((n + 3 : ℕ) : ℝ) + 1) ^ 2 * t) ≤ rexp (-16 * π * t) * rexp (-π * t) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : π * t * (16 + n) ≤ π * t * (((n + 3 : ℕ) : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith
  have e2 : rexp (-π * t) ^ n ≤ (1 / 2) ^ n := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    calc rexp (-π * t) ≤ rexp (-π) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ 1 / 2 := exp_neg_pi_le_half
  have e3 := mul_le_mul_of_nonneg_left e2 (Real.exp_pos (-16 * π * t)).le
  nlinarith [Real.exp_pos (-π * (((n + 3 : ℕ) : ℝ) + 1) ^ 2 * t)]

/-- **Tail bound.** For `t ≥ 1`, `0 ≤ θ(t) − 1 − Σ_{n<3} 2e^{−π(n+1)²t} ≤ 4 e^{−16πt}`. -/
theorem theta_tail_bound {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ evenKernel 0 t - 1 - ∑ n ∈ Finset.range 3, 2 * rexp (-π * (n + 1) ^ 2 * t) ∧
      evenKernel 0 t - 1 - ∑ n ∈ Finset.range 3, 2 * rexp (-π * (n + 1) ^ 2 * t) ≤
        4 * rexp (-16 * π * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have h := theta_sub_one_hasSum ht0
  rw [← hasSum_nat_add_iff' 3] at h
  have hg : HasSum (fun n : ℕ => 2 * rexp (-16 * π * t) * (1 / 2) ^ n) (4 * rexp (-16 * π * t)) := by
    have := (hasSum_geometric_two).mul_left (2 * rexp (-16 * π * t))
    rwa [show 2 * rexp (-16 * π * t) * 2 = 4 * rexp (-16 * π * t) by ring] at this
  refine ⟨?_, hasSum_le (fun n => term_le ht n) h hg⟩
  exact h.nonneg fun n => by positivity

end AEGIS.RHThetaTailV1

#print axioms AEGIS.RHThetaTailV1.theta_tail_bound
