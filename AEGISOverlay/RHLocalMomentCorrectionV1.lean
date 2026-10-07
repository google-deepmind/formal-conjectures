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
import RestrictedWeilCriterionKernelBridgeV10
import Mathlib.Topology.Order.Basic

/-!
# Two-moment correction of actual Weil packets

The two repository moments are the Mellin values at zero and one. Cramer's
rule therefore gives a support-preserving correction whenever two local
correctors have nonzero moment determinant. Two distinct translates of one
packet give such a determinant if both of its moments are nonzero.

The correction also preserves pointwise Mellin convergence to a moment-zero
target. This is a statement about moments and approximation, not the sign of
the Weil quadratic or its continuity in the pointwise Mellin topology.
-/

open Filter Topology Complex Set

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHLocalMomentCorrectionV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilZeroTranslationV11
open AEGIS.RestrictedWeilCriterionKernelBridgeV10

/-- The moment determinant of two actual packets. -/
def momentDet (u v : WeilCompactSmoothGV1) : ℂ :=
  mellin u.1 0 * mellin v.1 1 - mellin v.1 0 * mellin u.1 1

/-- The first Cramer coefficient. -/
def correctionA (f u v : WeilCompactSmoothGV1) : ℂ :=
  (mellin f.1 0 * mellin v.1 1 - mellin f.1 1 * mellin v.1 0) / momentDet u v

/-- The second Cramer coefficient. -/
def correctionB (f u v : WeilCompactSmoothGV1) : ℂ :=
  (mellin u.1 0 * mellin f.1 1 - mellin u.1 1 * mellin f.1 0) / momentDet u v

/-- Correct a packet using two packets with an invertible moment matrix. -/
def correctPacket (f u v : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  addPacket (addPacket f (scalePacket (-correctionA f u v) u))
    (scalePacket (-correctionB f u v) v)

theorem mellin_addPacket (f g : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (addPacket f g).1 s = mellin f.1 s + mellin g.1 s := by
  exact (hasMellin_add (weil_compact_smooth_mellin_convergent_all_v1 f s)
    (weil_compact_smooth_mellin_convergent_all_v1 g s)).2

theorem mellin_scalePacket (z : ℂ) (f : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (scalePacket z f).1 s = z * mellin f.1 s := by
  simpa only [scalePacket, smul_eq_mul] using mellin_const_smul f.1 s z

/-- The correction identity at every complex Mellin argument. -/
theorem mellin_correctPacket (f u v : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (correctPacket f u v).1 s =
      mellin f.1 s - correctionA f u v * mellin u.1 s -
        correctionB f u v * mellin v.1 s := by
  simp only [correctPacket, mellin_addPacket, mellin_scalePacket]
  ring

private theorem cramer_cancel (f₀ f₁ u₀ u₁ v₀ v₁ : ℂ)
    (hd : u₀ * v₁ - v₀ * u₁ ≠ 0) :
    (f₀ - (f₀ * v₁ - f₁ * v₀) / (u₀ * v₁ - v₀ * u₁) * u₀ -
      (u₀ * f₁ - u₁ * f₀) / (u₀ * v₁ - v₀ * u₁) * v₀ = 0) ∧
    (f₁ - (f₀ * v₁ - f₁ * v₀) / (u₀ * v₁ - v₀ * u₁) * u₁ -
      (u₀ * f₁ - u₁ * f₀) / (u₀ * v₁ - v₀ * u₁) * v₁ = 0) := by
  have hi := mul_inv_cancel₀ hd
  simp only [div_eq_mul_inv]
  constructor
  · linear_combination -f₀ * hi
  · linear_combination -f₁ * hi

/-- Exact local two-moment correction on the repository carrier. -/
theorem correctPacket_moments (f u v : WeilCompactSmoothGV1)
    (hd : momentDet u v ≠ 0) : WeilMomentConditionsV1 (correctPacket f u v) := by
  apply (moment_conditions_iff_mellin_endpoints_zero_v10 _).mpr
  simpa only [mellin_correctPacket, correctionA, correctionB, momentDet] using
    cramer_cancel (mellin f.1 0) (mellin f.1 1) (mellin u.1 0)
      (mellin u.1 1) (mellin v.1 0) (mellin v.1 1) hd

/-- Correction adds no support outside the three input supports. -/
theorem correctPacket_support (f u v : WeilCompactSmoothGV1) :
    tsupport (correctPacket f u v).1 ⊆ tsupport f.1 ∪ tsupport u.1 ∪ tsupport v.1 := by
  intro x hx
  rcases sum_support (addPacket f (scalePacket (-correctionA f u v) u))
      (scalePacket (-correctionB f u v) v) hx with hx | hx
  · rcases sum_support f (scalePacket (-correctionA f u v) u) hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr (scale_support _ _ hx))
  · exact Or.inr (scale_support _ _ hx)

/-- If all three inputs are supported in a local window, so is the correction. -/
theorem correctPacket_support_subset (f u v : WeilCompactSmoothGV1) (I : Set ℝ)
    (hf : tsupport f.1 ⊆ I) (hu : tsupport u.1 ⊆ I) (hv : tsupport v.1 ⊆ I) :
    tsupport (correctPacket f u v).1 ⊆ I := by
  intro x hx
  rcases correctPacket_support f u v hx with (hx | hx) | hx
  · exact hf hx
  · exact hu hx
  · exact hv hx

/-- A packet already satisfying the moments is unchanged by correction. -/
theorem correctPacket_eq_self (f u v : WeilCompactSmoothGV1)
    (hf : WeilMomentConditionsV1 f) : correctPacket f u v = f := by
  obtain ⟨h0, h1⟩ := (moment_conditions_iff_mellin_endpoints_zero_v10 f).mp hf
  apply Subtype.ext
  funext x
  simp [correctPacket, addPacket, scalePacket, correctionA, correctionB, h0, h1]

/-- The determinant of a packet and any centered real translate. -/
theorem momentDet_translate (u : WeilCompactSmoothGV1) (d : ℝ) :
    momentDet u (translatePacket u d) =
      mellin u.1 0 * mellin u.1 1 *
        ((Real.exp (d / 2) : ℂ) - (Real.exp (-d / 2) : ℂ)) := by
  have e0 : Complex.exp (((0 : ℂ) - 1 / 2) * (d : ℂ)) =
      (Real.exp (-d / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have e1 : Complex.exp (((1 : ℂ) - 1 / 2) * (d : ℂ)) =
      (Real.exp (d / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [momentDet, mellin_translatePacket_v11, e0, e1]
  ring

/-- Distinct real translates supply an invertible two-moment matrix. -/
theorem momentDet_translate_ne_zero (u : WeilCompactSmoothGV1) (d : ℝ)
    (h0 : mellin u.1 0 ≠ 0) (h1 : mellin u.1 1 ≠ 0) (hd : d ≠ 0) :
    momentDet u (translatePacket u d) ≠ 0 := by
  rw [momentDet_translate]
  apply mul_ne_zero (mul_ne_zero h0 h1)
  intro he
  have he' : Real.exp (d / 2) = Real.exp (-d / 2) :=
    Complex.ofReal_injective (sub_eq_zero.mp he)
  have := Real.exp_injective he'
  apply hd
  linarith

/-- Two local translates correct both moments of an arbitrary packet. -/
theorem translate_correctPacket_moments (f u : WeilCompactSmoothGV1) (d : ℝ)
    (h0 : mellin u.1 0 ≠ 0) (h1 : mellin u.1 1 ≠ 0) (hd : d ≠ 0) :
    WeilMomentConditionsV1 (correctPacket f u (translatePacket u d)) :=
  correctPacket_moments f u _ (momentDet_translate_ne_zero u d h0 h1 hd)

/-- Endpoint convergence suffices for the two correction coefficients to vanish. -/
theorem correction_coefficients_tendsto_zero (p : ℕ → WeilCompactSmoothGV1)
    (u v : WeilCompactSmoothGV1)
    (h0 : Tendsto (fun n => mellin (p n).1 0) atTop (𝓝 0))
    (h1 : Tendsto (fun n => mellin (p n).1 1) atTop (𝓝 0)) :
    Tendsto (fun n => correctionA (p n) u v) atTop (𝓝 0) ∧
      Tendsto (fun n => correctionB (p n) u v) atTop (𝓝 0) := by
  constructor
  · simpa only [correctionA, zero_mul, sub_zero, zero_div] using
      ((h0.mul_const (mellin v.1 1)).sub (h1.mul_const (mellin v.1 0))).div_const
        (momentDet u v)
  · simpa only [correctionB, mul_zero, sub_zero, zero_div] using
      ((h1.const_mul (mellin u.1 0)).sub (h0.const_mul (mellin u.1 1))).div_const
        (momentDet u v)

/-- Correcting an approximation preserves each convergent Mellin value. -/
theorem corrected_mellin_approximation (p : ℕ → WeilCompactSmoothGV1)
    (g u v : WeilCompactSmoothGV1) (s : ℂ) (hd : momentDet u v ≠ 0)
    (hg : WeilMomentConditionsV1 g)
    (h0 : Tendsto (fun n => mellin (p n).1 0) atTop (𝓝 (mellin g.1 0)))
    (h1 : Tendsto (fun n => mellin (p n).1 1) atTop (𝓝 (mellin g.1 1)))
    (hs : Tendsto (fun n => mellin (p n).1 s) atTop (𝓝 (mellin g.1 s))) :
    (∀ n, WeilMomentConditionsV1 (correctPacket (p n) u v)) ∧
      Tendsto (fun n => mellin (correctPacket (p n) u v).1 s)
        atTop (𝓝 (mellin g.1 s)) := by
  refine ⟨fun n => correctPacket_moments (p n) u v hd, ?_⟩
  obtain ⟨hg0, hg1⟩ := (moment_conditions_iff_mellin_endpoints_zero_v10 g).mp hg
  rw [hg0] at h0
  rw [hg1] at h1
  obtain ⟨ha, hb⟩ := correction_coefficients_tendsto_zero p u v h0 h1
  simpa only [mellin_correctPacket, zero_mul, sub_zero] using
    (hs.sub (ha.mul_const (mellin u.1 s))).sub (hb.mul_const (mellin v.1 s))

#print axioms AEGIS.RHLocalMomentCorrectionV1.correctPacket_moments
#print axioms AEGIS.RHLocalMomentCorrectionV1.correctPacket_support_subset
#print axioms AEGIS.RHLocalMomentCorrectionV1.momentDet_translate_ne_zero
#print axioms AEGIS.RHLocalMomentCorrectionV1.corrected_mellin_approximation

end AEGIS.RHLocalMomentCorrectionV1
