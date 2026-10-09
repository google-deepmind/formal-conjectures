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

import RHTranslateSpectralObstructionV1

/-!
# Shared complex Mellin zeros of multiple generators

Arbitrary finite combinations may use a different generator and shift in every
term. A common complex Mellin zero still survives. The excluded target is the
actual repository moment-zero packet from the residue-witness construction.

Real-frequency nonvanishing alone does not rule out this obstruction: the
polynomial `z^2 + 1` is positive on the real axis and vanishes at `I`.
-/

open Filter Topology Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHMultiGeneratorMellinObstructionV1

open AEGIS.RHTranslateSpectralObstructionV1
open AEGIS.RHGramExpansionV13
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilZeroTranslationV11
open AEGIS.RestrictedWeilCriterionResidueWitnessV11

/-- Finite combinations of translated members of an arbitrary generator family. -/
def MultiTranslateSpanPacket {ι : Type*}
    (gs : ι → WeilCompactSmoothGV1) (p : WeilCompactSmoothGV1) : Prop :=
  ∃ (n : ℕ) (pick : Fin (n + 1) → ι) (d : Fin (n + 1) → ℝ)
    (z : Fin (n + 1) → ℂ),
    p = packetSum z (fun i => translatePacket (gs (pick i)) (d i))

/-- Common complex Mellin zeros survive arbitrary finite multigenerator synthesis. -/
theorem multi_translate_mellin_zero {ι : Type*}
    (gs : ι → WeilCompactSmoothGV1) (s : ℂ)
    (hs : ∀ i, mellin (gs i).1 s = 0)
    (p : WeilCompactSmoothGV1) (hp : MultiTranslateSpanPacket gs p) :
    mellin p.1 s = 0 := by
  obtain ⟨n, pick, d, z, rfl⟩ := hp
  apply packetSum_mellin_zero
  intro i
  rw [mellin_translatePacket_v11, hs, mul_zero]

/-- A common extra complex zero obstructs approximation even with arbitrarily
many complementary real-frequency generators. -/
theorem common_complex_zero_obstructs_approximation {ι : Type*}
    (gs : ι → WeilCompactSmoothGV1) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hs : ∀ i, mellin (gs i).1 s = 0) :
    ∃ f : WeilCompactSmoothGV1, WeilMomentConditionsV1 f ∧
      ∀ p : ℕ → WeilCompactSmoothGV1,
        (∀ k, MultiTranslateSpanPacket gs (p k)) →
        ¬ Tendsto (fun k => mellin (p k).1 s) atTop (𝓝 (mellin f.1 s)) := by
  refine ⟨TargetPacketV11 s, targetPacket_moments_v11 s, ?_⟩
  intro p hp
  exact not_mellin_convergent_of_common_zero p (TargetPacketV11 s) s
    (fun k => multi_translate_mellin_zero gs s hs (p k) (hp k))
    (targetPacket_mellin_target_ne_zero_v11 s hs0 hs1)

/-- Positivity of a multiplier on the real axis does not exclude complex zeros. -/
theorem real_positive_multiplier_has_complex_zero :
    (∀ t : ℝ, 0 < t ^ 2 + 1) ∧ (I ^ 2 + 1 : ℂ) = 0 := by
  constructor
  · intro t
    positivity
  · norm_num

end AEGIS.RHMultiGeneratorMellinObstructionV1

#print axioms AEGIS.RHMultiGeneratorMellinObstructionV1.multi_translate_mellin_zero
#print axioms AEGIS.RHMultiGeneratorMellinObstructionV1.common_complex_zero_obstructs_approximation
#print axioms AEGIS.RHMultiGeneratorMellinObstructionV1.real_positive_multiplier_has_complex_zero
