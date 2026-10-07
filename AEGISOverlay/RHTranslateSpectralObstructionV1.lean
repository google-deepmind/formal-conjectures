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

import WeilZeroTranslationV11
import RHGramExpansionV13
import RestrictedWeilCriterionResidueWitnessV11
import Mathlib.Topology.Order.Basic

/-!
# Mellin zeros retained by translates of a fixed packet

The repository transport law `WeilZeroTranslationV11.mellin_translatePacket_v11`
shows that every finite linear combination of translates retains a Mellin zero
of its mother packet. A limit preserves that zero whenever its Mellin values
converge. This applies to arbitrary real shifts, including any dense subgroup.
-/

open Filter Topology Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHTranslateSpectralObstructionV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilZeroTranslationV11
open AEGIS.RHGramExpansionV13
open AEGIS.RestrictedWeilCriterionResidueWitnessV11

/-- Complex scaling preserves any specified Mellin zero. -/
theorem scale_mellin_zero (g : WeilCompactSmoothGV1) (s z : ℂ)
    (hg : mellin g.1 s = 0) : mellin (scalePacket z g).1 s = 0 := by
  change mellin (fun x : ℝ => z * g.1 x) s = 0
  simpa [smul_eq_mul, hg] using mellin_const_smul g.1 s z

/-- Addition preserves any common Mellin zero. -/
theorem add_mellin_zero (g h : WeilCompactSmoothGV1) (s : ℂ)
    (hg : mellin g.1 s = 0) (hh : mellin h.1 s = 0) :
    mellin (addPacket g h).1 s = 0 := by
  have hsum := hasMellin_add
    (weil_compact_smooth_mellin_convergent_all_v1 g s)
    (weil_compact_smooth_mellin_convergent_all_v1 h s)
  change mellin (fun x : ℝ => g.1 x + h.1 x) s = 0
  rw [hsum.2, hg, hh, add_zero]

/-- A finite packet sum retains each common Mellin zero of its inputs. -/
theorem packetSum_mellin_zero {n : ℕ} (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (s : ℂ)
    (hs : ∀ i, mellin (gs i).1 s = 0) :
    mellin (packetSum z gs).1 s = 0 := by
  induction n with
  | zero => exact scale_mellin_zero (gs 0) s (z 0) (hs 0)
  | succ n ih =>
    exact add_mellin_zero _ _ s
      (ih (fun i => z i.castSucc) (fun i => gs i.castSucc) (fun i => hs i.castSucc))
      (scale_mellin_zero _ s _ (hs (Fin.last (n + 1))))

/-- Finite combinations of arbitrary translates preserve a mother's Mellin zero. -/
theorem translate_sum_mellin_zero {n : ℕ} (g : WeilCompactSmoothGV1)
    (s : ℂ) (hg : mellin g.1 s = 0) (d : Fin (n + 1) → ℝ)
    (z : Fin (n + 1) → ℂ) :
    mellin (packetSum z (fun i => translatePacket g (d i))).1 s = 0 := by
  apply packetSum_mellin_zero
  intro i
  rw [mellin_translatePacket_v11, hg, mul_zero]

/-- Mellin-convergent limits cannot remove the common spectral zero. -/
theorem mellin_zero_of_limit (p : ℕ → WeilCompactSmoothGV1)
    (g : WeilCompactSmoothGV1) (s : ℂ)
    (hp : ∀ n, mellin (p n).1 s = 0)
    (hlim : Tendsto (fun n => mellin (p n).1 s) atTop (𝓝 (mellin g.1 s))) :
    mellin g.1 s = 0 := by
  have hzero : Tendsto (fun n => mellin (p n).1 s) atTop (𝓝 (0 : ℂ)) := by
    simpa only [hp] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hzero

/-- A nonzero target Mellin value obstructs approximation with a shared spectral zero. -/
theorem not_mellin_convergent_of_common_zero (p : ℕ → WeilCompactSmoothGV1)
    (g : WeilCompactSmoothGV1) (s : ℂ)
    (hp : ∀ n, mellin (p n).1 s = 0) (hg : mellin g.1 s ≠ 0) :
    ¬ Tendsto (fun n => mellin (p n).1 s) atTop (𝓝 (mellin g.1 s)) := by
  intro hlim
  exact hg (mellin_zero_of_limit p g s hp hlim)

/-- Membership in a finite linear combination of arbitrary real translates. -/
def TranslateSpanPacket (g p : WeilCompactSmoothGV1) : Prop :=
  ∃ (n : ℕ) (d : Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℂ),
    p = packetSum z (fun i => translatePacket g (d i))

/-- Each extra Mellin zero excludes an explicit moment-zero target packet
from the Mellin-convergent closure of all finite translates of the mother. -/
theorem extra_mellin_zero_obstructs_universal_approximation
    (g : WeilCompactSmoothGV1) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hg : mellin g.1 s = 0) :
    ∃ f : WeilCompactSmoothGV1, WeilMomentConditionsV1 f ∧
      ∀ p : ℕ → WeilCompactSmoothGV1,
        (∀ k, TranslateSpanPacket g (p k)) →
        ¬ Tendsto (fun k => mellin (p k).1 s) atTop (𝓝 (mellin f.1 s)) := by
  refine ⟨TargetPacketV11 s, targetPacket_moments_v11 s, ?_⟩
  intro p hp
  apply not_mellin_convergent_of_common_zero p (TargetPacketV11 s) s
  · intro k
    obtain ⟨n, d, z, heq⟩ := hp k
    rw [heq]
    exact translate_sum_mellin_zero g s hg d z
  · exact targetPacket_mellin_target_ne_zero_v11 s hs0 hs1

#print axioms AEGIS.RHTranslateSpectralObstructionV1.translate_sum_mellin_zero
#print axioms AEGIS.RHTranslateSpectralObstructionV1.not_mellin_convergent_of_common_zero
#print axioms AEGIS.RHTranslateSpectralObstructionV1.extra_mellin_zero_obstructs_universal_approximation

end AEGIS.RHTranslateSpectralObstructionV1
