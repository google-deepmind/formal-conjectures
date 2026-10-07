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

import WeilMomentAnnihilatorV1
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
AEGIS Ω — strict-strip Mellin seed V11.

This is the first genuinely new existence lemma needed by the reverse
restricted-Weil criterion.

Given two complex points s₁,s₂, construct one compact-smooth packet supported
in a small neighborhood of x=1 such that both Mellin values are nonzero.
The support is chosen inside the region where both Mellin kernels have real
part > 1/2. A nonnegative smooth bump with value 1 at x=1 then makes both
Mellin integrals have strictly positive real part.

Composing this seed with the existing finite-dilation moment annihilator
produces an exact two-moment packet without destroying either strict-strip
Mellin evaluation.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Topology ContDiff

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilStrictStripSeedV11

def MellinKernelReV11 (s : ℂ) (x : ℝ) : ℝ :=
  ((x : ℂ) ^ (s - 1)).re

private theorem mellinKernelRe_continuousAt_one_v11 (s : ℂ) :
    ContinuousAt (MellinKernelReV11 s) 1 := by
  unfold MellinKernelReV11
  exact
    (Complex.continuousAt_ofReal_cpow_const
      1 (s - 1) (Or.inr one_ne_zero)).re

@[simp] theorem mellinKernelRe_one_v11 (s : ℂ) :
    MellinKernelReV11 s 1 = 1 := by
  simp [MellinKernelReV11]

/-- A single bump can make two prescribed Mellin evaluations nonzero. -/
theorem exists_compact_smooth_seed_two_mellin_ne_zero_v11
    (s₁ s₂ : ℂ) :
    ∃ f : WeilCompactSmoothGV1,
      mellin f.1 s₁ ≠ 0 ∧ mellin f.1 s₂ ≠ 0 := by
  let S : Set ℝ := {x : ℝ |
    0 < x ∧
    (1 / 2 : ℝ) < MellinKernelReV11 s₁ x ∧
    (1 / 2 : ℝ) < MellinKernelReV11 s₂ x}

  have hK1 :
      ∀ᶠ x : ℝ in 𝓝 (1 : ℝ),
        (1 / 2 : ℝ) < MellinKernelReV11 s₁ x := by
    exact
      (mellinKernelRe_continuousAt_one_v11 s₁).eventually
        (Ioi_mem_nhds (by simp [mellinKernelRe_one_v11]))

  have hK2 :
      ∀ᶠ x : ℝ in 𝓝 (1 : ℝ),
        (1 / 2 : ℝ) < MellinKernelReV11 s₂ x := by
    exact
      (mellinKernelRe_continuousAt_one_v11 s₂).eventually
        (Ioi_mem_nhds (by simp [mellinKernelRe_one_v11]))

  have hS : S ∈ 𝓝 (1 : ℝ) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num),
      hK1, hK2] with x hx hk1 hk2
    exact ⟨hx, hk1, hk2⟩

  obtain ⟨η, hηsupp, hηcompact, hηsmooth, hηrange, hη1⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hS

  have hηcont : Continuous η := hηsmooth.continuous
  have hηnonneg : ∀ x : ℝ, 0 ≤ η x := by
    intro x
    exact (hηrange (mem_range_self x)).1

  let seedFn : ℝ → ℂ := Complex.ofRealCLM ∘ η

  have hseedSmooth : ContDiff ℝ ∞ seedFn := by
    exact Complex.ofRealCLM.contDiff.comp hηsmooth

  have hseedCompact : HasCompactSupport seedFn := by
    dsimp [seedFn]
    exact hηcompact.comp_left rfl

  have hseedPositive : tsupport seedFn ⊆ Ioi (0 : ℝ) := by
    dsimp [seedFn]
    refine (tsupport_comp_subset rfl η).trans ?_
    intro x hx
    exact (hηsupp hx).1

  let seed : WeilCompactSmoothGV1 :=
    ⟨seedFn, hseedSmooth, hseedCompact, hseedPositive⟩

  have seed_coe (x : ℝ) : seed.1 x = (η x : ℂ) := by
    rfl

  have kernel_integral_pos
      (s : ℂ)
      (hsupp : ∀ x ∈ tsupport η,
        (1 / 2 : ℝ) < MellinKernelReV11 s x) :
      0 <
        ∫ x in Ioi (0 : ℝ),
          MellinKernelReV11 s x * η x := by

    let r : ℝ → ℝ := fun x => MellinKernelReV11 s x * η x

    have hr_cont : Continuous r := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx : 0 < x
      · exact
          ((Complex.continuousAt_ofReal_cpow_const
            x (s - 1) (Or.inr hx.ne')).re.mul hηcont.continuousAt)
      · have hxnot : x ∉ tsupport η := by
          intro hxt
          have hpos := (hηsupp hxt).1
          exact (not_lt_of_ge (le_of_not_gt hx)) hpos
        have hopen : (tsupport η)ᶜ ∈ 𝓝 x :=
          isOpen_compl_iff.mpr isClosed_tsupport |>.mem_nhds hxnot
        have heq :
            r =ᶠ[𝓝 x] (fun _ : ℝ => 0) :=
          eventually_of_mem hopen (fun y hy => by
            have hη0 : η y = 0 :=
              image_eq_zero_of_notMem_tsupport hy
            simp [r, hη0])
        exact ContinuousAt.congr_of_eventuallyEq continuousAt_const heq.symm

    have hr_comp : HasCompactSupport r := by
      dsimp [r]
      exact HasCompactSupport.mul_left hηcompact

    have hr_nonneg : 0 ≤ r := by
      intro x
      by_cases hηx : η x = 0
      · simp [r, hηx]
      · have hxt : x ∈ tsupport η := subset_tsupport η hηx
        have hk := hsupp x hxt
        have hk0 : 0 ≤ MellinKernelReV11 s x := by linarith
        exact mul_nonneg hk0 (hηnonneg x)

    have hr_one : r 1 ≠ 0 := by
      simp [r, mellinKernelRe_one_v11, hη1]

    have hfull : 0 < ∫ x : ℝ, r x :=
      hr_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero
        hr_comp hr_nonneg hr_one

    have hout : ∀ x ∉ Ioi (0 : ℝ), r x = 0 := by
      intro x hx
      have hxnot : x ∉ tsupport η := by
        intro hxt
        exact hx (hηsupp hxt).1
      have hη0 : η x = 0 :=
        image_eq_zero_of_notMem_tsupport hxnot
      simp [r, hη0]

    have hset :
        (∫ x in Ioi (0 : ℝ), r x) = ∫ x : ℝ, r x := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr
      intro x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · simp [hx]
      · simp [hx, hout x hx]

    rw [hset]
    exact hfull

  have hmellin_re
      (s : ℂ) :
      (mellin seed.1 s).re =
        ∫ x in Ioi (0 : ℝ),
          MellinKernelReV11 s x * η x := by
    have hconv : MellinConvergent seed.1 s :=
      weil_compact_smooth_mellin_convergent_all_v1 seed s
    unfold mellin
    have hre := integral_re hconv
    rw [hre]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [seed_coe]
    change
      (((x : ℂ) ^ (s - 1)) * (η x : ℂ)).re =
        MellinKernelReV11 s x * η x
    simp [MellinKernelReV11, Complex.mul_re]

  have hpos1 :
      0 < (mellin seed.1 s₁).re := by
    rw [hmellin_re s₁]
    exact kernel_integral_pos s₁ (fun x hx => (hηsupp hx).2.1)

  have hpos2 :
      0 < (mellin seed.1 s₂).re := by
    rw [hmellin_re s₂]
    exact kernel_integral_pos s₂ (fun x hx => (hηsupp hx).2.2)

  refine ⟨seed, ?_, ?_⟩
  · intro h
    rw [h] at hpos1
    simp at hpos1
  · intro h
    rw [h] at hpos2
    simp at hpos2

/-- NEW PRODUCER: for any two points in the strict critical strip, there is an
exact repository moment-zero packet whose Mellin transform is nonzero at both
points. -/
theorem exists_moment_zero_seed_two_strip_points_v11
    (s₁ s₂ : ℂ)
    (h10 : 0 < s₁.re) (h11 : s₁.re < 1)
    (h20 : 0 < s₂.re) (h21 : s₂.re < 1) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      mellin g.1 s₁ ≠ 0 ∧
      mellin g.1 s₂ ≠ 0 := by
  obtain ⟨f, hf1, hf2⟩ :=
    exists_compact_smooth_seed_two_mellin_ne_zero_v11 s₁ s₂
  refine ⟨WeilMomentAnnihilatorV1 f,
    weil_moment_annihilator_moments_v1 f, ?_, ?_⟩
  · exact
      weil_moment_annihilator_mellin_ne_zero_v1
        f h10 h11 hf1
  · exact
      weil_moment_annihilator_mellin_ne_zero_v1
        f h20 h21 hf2

end AEGIS.WeilStrictStripSeedV11

#print axioms AEGIS.WeilStrictStripSeedV11.exists_compact_smooth_seed_two_mellin_ne_zero_v11
#print axioms AEGIS.WeilStrictStripSeedV11.exists_moment_zero_seed_two_strip_points_v11
