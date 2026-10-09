import RestrictedWeilCriterionResidueCoefficientV11
import RHZeroKernelLaplaceAnalyticV12
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-!
AEGIS Ω — local pole contradiction for the restricted-Weil terminal v13.

This module is deliberately generic.  It proves the local analytic fact needed
at the end of the restricted-Weil argument: a function continuous at z cannot
agree on a punctured neighbourhood with a nonzero simple pole plus a function
continuous at z.

No RH conclusion is asserted here.
AUTHORITY_EFFECT = NONE.
-/

open Set Filter Complex
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionFinalV13

theorem continuous_cannot_equal_nonzero_simple_pole_v13
    {F H : ℂ → ℂ} {z c : ℂ}
    (hF : ContinuousAt F z)
    (hH : ContinuousAt H z)
    (hc : c ≠ 0)
    (heq : F =ᶠ[𝓝[≠] z] fun w => c / (w - z) + H w) :
    False := by
  have hsub :
      Tendsto (fun w : ℂ => w - z) (𝓝[≠] z) (𝓝 0) := by
    have h :
        Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 (z - z)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using h.mono_left nhdsWithin_le_nhds

  have hFlim :
      Tendsto (fun w : ℂ => (w - z) * F w) (𝓝[≠] z) (𝓝 0) := by
    simpa using
      hsub.mul (hF.tendsto.mono_left nhdsWithin_le_nhds)

  have hHlim :
      Tendsto (fun w : ℂ => (w - z) * H w) (𝓝[≠] z) (𝓝 0) := by
    simpa using
      hsub.mul (hH.tendsto.mono_left nhdsWithin_le_nhds)

  have heqmul :
      (fun w : ℂ => (w - z) * F w) =ᶠ[𝓝[≠] z]
        (fun w => c + (w - z) * H w) := by
    filter_upwards [heq, self_mem_nhdsWithin] with w hw hne
    have hwz : w ≠ z := by simpa using hne
    have hdiff : w - z ≠ 0 := sub_ne_zero.mpr hwz
    rw [hw]
    field_simp [hdiff]
    <;> ring

  have hRlim :
      Tendsto (fun w : ℂ => c + (w - z) * H w) (𝓝[≠] z) (𝓝 c) := by
    simpa using tendsto_const_nhds.add hHlim

  have hFlimC :
      Tendsto (fun w : ℂ => (w - z) * F w) (𝓝[≠] z) (𝓝 c) :=
    hRlim.congr' heqmul.symm

  have hzero : (0 : ℂ) = c :=
    tendsto_nhds_unique hFlim hFlimC
  exact hc hzero.symm

end AEGIS.RestrictedWeilCriterionFinalV13

#print axioms AEGIS.RestrictedWeilCriterionFinalV13.continuous_cannot_equal_nonzero_simple_pole_v13
