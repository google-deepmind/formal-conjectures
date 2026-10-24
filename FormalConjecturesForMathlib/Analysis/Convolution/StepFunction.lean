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

public import Mathlib.Analysis.Convolution

@[expose] public section

/-!
# Autoconvolution of step functions on `[0, 1]`

A step function with `n` equal cells on `[0, 1]` and heights `c` has a piecewise-linear
autoconvolution. Its supremum is at most `max_k b_k / n`, where `b` is the discrete
autoconvolution of `c`. This holds because the tents `1_I ⋆ 1_J` form a partition of unity.

## Main definitions

* `StepFunction.step n c`: the step function with height `c i` on `[i/n, (i+1)/n)`.

## Main results

* `StepFunction.step_conv_le`: the pointwise bound on `step n c ⋆ step n c`.
* `StepFunction.integral_step`: `∫ step n c = (∑ c i) / n`.

*References:*
- [MV10](https://arxiv.org/abs/0907.1379)
  M. Matolcsi and C. Vinuesa, *Improved bounds on the supremum of autoconvolutions*,
  J. Math. Anal. Appl. 372 (2010), 439-447, §4.
-/

namespace StepFunction

open MeasureTheory Set
open scoped Convolution

/-- Clamp to `[0, 1]`. -/
noncomputable def ramp (z : ℝ) : ℝ := max 0 (min 1 z)

lemma ramp_nonneg (z : ℝ) : 0 ≤ ramp z := le_max_left _ _

lemma ramp_le_one (z : ℝ) : ramp z ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma ramp_mono {y z : ℝ} (h : y ≤ z) : ramp y ≤ ramp z :=
  max_le_max le_rfl (min_le_min le_rfl h)

/-- The length of `[a, a + h) ∩ (x - [b, b + h))` is a tent in `x`. -/
lemma overlap_eq (a b x h : ℝ) (hh : 0 < h) :
    max (min (a + h) (x - b) - max a (x - b - h)) 0 =
      h * (ramp ((x - a - b) / h) - ramp ((x - a - b) / h - 1)) := by
  obtain ⟨z, rfl⟩ : ∃ z, x = a + b + h * z := ⟨(x - a - b) / h, by field_simp; ring⟩
  have hz : (a + b + h * z - a - b) / h = z := by field_simp; ring
  rw [hz, show a + b + h * z - b = a + h * z by ring]
  have e1 : min (a + h) (a + h * z) = a + h * min 1 z := by
    rw [mul_min_of_nonneg _ _ hh.le, ← min_add_add_left, mul_one]
  have e2 : max a (a + h * z - h) = a + h * max 0 (z - 1) := by
    rw [mul_max_of_nonneg _ _ hh.le, ← max_add_add_left]; congr 1 <;> ring
  have e3 : ∀ u, max (h * u) 0 = h * max u 0 := fun u ↦ by
    rw [mul_max_of_nonneg _ _ hh.le, mul_zero]
  rw [e1, e2, show a + h * min 1 z - (a + h * max 0 (z - 1)) = h * (min 1 z - max 0 (z - 1)) by
    ring, e3]
  congr 1
  simp only [ramp, min_def, max_def]
  split_ifs <;> linarith

/-- The step function with height `c i` on the cell `[i/n, (i+1)/n)`, for `i < n`. -/
noncomputable def step (n : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (Ico ((i : ℝ) / n) ((i + 1) / n)).indicator (fun _ ↦ c i) x

lemma step_nonneg (n : ℕ) {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i) (x : ℝ) : 0 ≤ step n c x :=
  Finset.sum_nonneg fun i _ ↦ indicator_nonneg (fun _ _ ↦ hc i) _

lemma integrable_indicator_cell (n : ℕ) (c : ℕ → ℝ) (i : ℕ) :
    Integrable ((Ico ((i : ℝ) / n) ((i + 1) / n)).indicator (fun _ ↦ c i)) :=
  (integrable_indicator_iff measurableSet_Ico).2
    (integrableOn_const measure_Ico_lt_top.ne)

lemma integrable_step (n : ℕ) (c : ℕ → ℝ) : Integrable (step n c) :=
  integrable_finsetSum _ fun i _ ↦ integrable_indicator_cell n c i

lemma support_step_subset (n : ℕ) (c : ℕ → ℝ) :
    Function.support (step n c) ⊆ Icc 0 1 := by
  intro x hx
  by_contra hx'
  refine hx (Finset.sum_eq_zero fun i hi ↦ indicator_of_notMem (fun h ↦ hx' ?_) _)
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
  have hn' : (0 : ℝ) < n := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
  obtain ⟨h1, h2⟩ := h
  refine ⟨(by positivity : (0 : ℝ) ≤ i / n).trans h1, h2.le.trans ?_⟩
  rwa [div_le_one hn']

lemma integral_step (n : ℕ) (hn : 0 < n) (c : ℕ → ℝ) :
    ∫ x, step n c x = (∑ i ∈ Finset.range n, c i) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold step
  rw [integral_finsetSum _ fun i _ ↦ integrable_indicator_cell n c i]
  simp only [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico, smul_eq_mul]
  have : ∀ i : ℕ, max (((i : ℝ) + 1) / n - i / n) 0 = 1 / n := fun i ↦ by
    rw [← sub_div, add_sub_cancel_left, max_eq_left (by positivity)]
  simp only [this, ← Finset.mul_sum]
  field_simp

/-- The set of `t` with `t` in cell `i` and `x - t` in cell `j`. -/
def pairSet (n : ℕ) (x : ℝ) (i j : ℕ) : Set ℝ :=
  Ico ((i : ℝ) / n) ((i + 1) / n) ∩ (fun t ↦ x - t) ⁻¹' Ico ((j : ℝ) / n) ((j + 1) / n)

lemma measurableSet_pairSet (n : ℕ) (x : ℝ) (i j : ℕ) : MeasurableSet (pairSet n x i j) :=
  measurableSet_Ico.inter (measurableSet_Ico.preimage (by fun_prop))

lemma step_mul_step (n : ℕ) (c : ℕ → ℝ) (x t : ℝ) :
    step n c t * step n c (x - t) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (pairSet n x i j).indicator (fun _ ↦ c i * c j) t := by
  simp only [step, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [pairSet, indicator, mem_inter_iff, mem_preimage]
  split_ifs <;> simp_all

/-- The value of the tent `τ_k` at `y = n x`. -/
noncomputable def tent (y : ℝ) (k : ℕ) : ℝ := ramp (y - k) - ramp (y - k - 1)

lemma tent_nonneg (y : ℝ) (k : ℕ) : 0 ≤ tent y k :=
  sub_nonneg.2 (ramp_mono (by linarith))

lemma sum_tent_le_one (y : ℝ) (N : ℕ) : ∑ k ∈ Finset.range N, tent y k ≤ 1 := by
  have := Finset.sum_range_sub' (fun k : ℕ ↦ ramp (y - k)) N
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, ← sub_sub] at this
  rw [show (∑ k ∈ Finset.range N, tent y k) = _ from this]
  have := ramp_nonneg (y - N); have := ramp_le_one y
  linarith

lemma measureReal_pairSet_le (n : ℕ) (hn : 0 < n) (x : ℝ) (i j : ℕ) :
    volume.real (pairSet n x i j) ≤ tent (n * x) (i + j) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : pairSet n x i j ⊆
      Icc (max ((i : ℝ) / n) (x - j / n - 1 / n)) (min ((i : ℝ) / n + 1 / n) (x - j / n)) := by
    rintro t ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨max_le h1 ?_, le_min ?_ ?_⟩
    · rw [add_div] at h4; linarith
    · rw [add_div] at h2; linarith
    · linarith
  refine (measureReal_mono hsub measure_Icc_lt_top.ne).trans ?_
  rw [Real.volume_real_Icc, overlap_eq _ _ _ _ (by positivity), tent]
  have : (x - i / n - j / n) / (1 / n) = n * x - (i + j : ℕ) := by
    push_cast; field_simp; ring
  rw [this]
  field_simp
  ring_nf
  rfl

/-- The pointwise bound on the autoconvolution of a step function. -/
theorem step_conv_le (n : ℕ) (hn : 0 < n) (c : ℕ → ℝ) (M : ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hM : ∀ k < 2 * n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if i + j = k then c i * c j else 0) ≤ M) (x : ℝ) :
    (step n c ⋆ step n c) x ≤ M / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : 0 ≤ M := by
    refine le_trans ?_ (hM 0 (by omega))
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (hc i) (hc j)
  have hint : ∀ i j, Integrable ((pairSet n x i j).indicator (fun _ ↦ c i * c j)) := by
    intro i j
    refine (integrable_indicator_iff (measurableSet_pairSet n x i j)).2 (integrableOn_const ?_)
    refine ne_top_of_le_ne_top
      (measure_Ico_lt_top (μ := volume) (a := (i : ℝ) / n) (b := (i + 1) / n)).ne ?_
    exact measure_mono inter_subset_left
  set y := (n : ℝ) * x
  calc (step n c ⋆ step n c) x
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          volume.real (pairSet n x i j) * (c i * c j) := by
        rw [convolution_lsmul]
        simp only [smul_eq_mul, step_mul_step]
        rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [integral_finsetSum _ fun j _ ↦ hint i j]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [integral_indicator_const _ (measurableSet_pairSet n x i j), smul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, tent y (i + j) / n * (c i * c j) := by
        gcongr with i _ j _
        · exact mul_nonneg (hc i) (hc j)
        · exact measureReal_pairSet_le n hn x i j
    _ = (∑ k ∈ Finset.range (2 * n), (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          (if i + j = k then c i * c j else 0)) * tent y k) / n := by
        symm
        rw [Finset.sum_div]
        simp only [Finset.sum_mul, Finset.sum_div]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        simp only [ite_mul, zero_mul, ite_div, zero_div]
        rw [Finset.sum_ite_eq, if_pos]
        · ring
        · simp only [Finset.mem_range] at hi hj ⊢; omega
    _ ≤ (∑ k ∈ Finset.range (2 * n), M * tent y k) / n := by
        gcongr with k hk
        · exact tent_nonneg y k
        · exact hM k (Finset.mem_range.1 hk)
    _ ≤ M / n := by
        rw [← Finset.mul_sum]
        gcongr
        exact mul_le_of_le_one_right hM0 (sum_tent_le_one y _)

lemma step_conv_nonneg (n : ℕ) {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i) (x : ℝ) :
    0 ≤ (step n c ⋆ step n c) x := by
  rw [convolution_lsmul]
  exact integral_nonneg fun t ↦ smul_nonneg (step_nonneg n hc t) (step_nonneg n hc _)

/-- The double sum over `i, j < n` with `i + j = k` is the discrete autoconvolution at `k`. -/
lemma sum_ite_add_eq {R : Type*} [CommSemiring R] (n k : ℕ) (g : ℕ → R)
    (hg : ∀ i, n ≤ i → g i = 0) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i + j = k then g i * g j else 0) =
      ∑ i ∈ Finset.range (k + 1), g i * g (k - i) := by
  have hin : ∀ i, ∑ j ∈ Finset.range n, (if i + j = k then g i * g j else 0) =
      if i ≤ k then g i * g (k - i) else 0 := by
    intro i
    split_ifs with hik
    · by_cases hkn : k - i < n
      · rw [Finset.sum_eq_single (k - i)]
        · rw [if_pos (by omega)]
        · intro j _ hj; rw [if_neg (by omega)]
        · intro h; exact absurd (Finset.mem_range.2 hkn) h
      · rw [hg (k - i) (by omega), mul_zero]
        exact Finset.sum_eq_zero fun j hj ↦ by
          rw [Finset.mem_range] at hj; rw [if_neg (by omega)]
    · exact Finset.sum_eq_zero fun j _ ↦ by rw [if_neg (by omega)]
  simp only [hin]
  rw [← Finset.sum_filter]
  refine Finset.sum_subset
    (fun i ↦ by simp only [Finset.mem_filter, Finset.mem_range]; omega) fun i hi hni ↦ ?_
  simp only [Finset.mem_range, Finset.mem_filter] at hi hni
  rw [hg i (by omega), zero_mul]

end StepFunction
