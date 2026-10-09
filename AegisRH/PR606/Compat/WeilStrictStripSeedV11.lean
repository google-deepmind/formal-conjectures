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
import WeilOffLineSeedV10
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
AEGIS Ω — strict-strip Mellin seed V11.

The public two-point seed statements are unchanged. Their existence proof
reuses the exact V10 packet producer already present in the PR606 closure,
rather than duplicating the bump-integral argument. The legacy real-kernel
definition and its lemmas are retained for compatibility.

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
  exact Complex.continuous_re.continuousAt.comp
    (Complex.continuousAt_ofReal_cpow_const
      1 (s - 1) (Or.inr one_ne_zero))

@[simp] theorem mellinKernelRe_one_v11 (s : ℂ) :
    MellinKernelReV11 s 1 = 1 := by
  simp [MellinKernelReV11]

/-- A single bump can make two prescribed Mellin evaluations nonzero. -/
theorem exists_compact_smooth_seed_two_mellin_ne_zero_v11
    (s₁ s₂ : ℂ) :
    ∃ f : WeilCompactSmoothGV1,
      mellin f.1 s₁ ≠ 0 ∧ mellin f.1 s₂ ≠ 0 := by
  exact AEGIS.WeilOffLineSeedV10.exists_packet_mellin_ne_zero_pair_v10 s₁ s₂

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
