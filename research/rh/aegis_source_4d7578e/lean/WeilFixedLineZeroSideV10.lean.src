import WeilPairedZeroEvaluationV9
import WeilPairedHadamardTsumFusionV1
import WeilZeroCarrierBridgeV10
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic

/-!
AEGIS Ω — paired zero-side fixed-line assembly V10.

This module composes:
* V5 fixed-line paired-Hadamard/Fubini assembly;
* the re-bound paired-kernel tsum fusion;
* V9 paired-zero integral evaluation;
* the public V10 AEGIS/LiCriterion zero-carrier equivalence;
* the provider involution rho ↦ 1-rho and multiplicity preservation.

The result identifies the normalized fixed-line xi log-derivative integral with
the canonical multiplicity-weighted AEGIS zeta-zero tsum.

AUTHORITY_EFFECT = NONE.
-/

open Complex Filter MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFixedLineZeroSideV10

open AEGIS.WeilPairedZeroEvaluationV9
open AEGIS.WeilZeroCarrierBridgeV10

def XiMellinZeroTermV10
    (f : ℝ → ℂ) (rho : LiCriterion.NontrivialZero) : ℂ :=
  (analyticOrderNatAt LiCriterion.riemannXi rho.val : ℂ) *
    mellin f rho.val

def XiPairedMellinZeroTermV10
    (f : ℝ → ℂ) (rho : LiCriterion.NontrivialZero) : ℂ :=
  (analyticOrderNatAt LiCriterion.riemannXi rho.val : ℂ) *
    (mellin f rho.val + mellin f (1 - rho.val))

/-- Summability of the provider-indexed zero functional follows by reindexing
the already-proved AEGIS canonical zero sum through the public carrier
equivalence. -/
theorem xi_mellin_zero_summable_v10
    (f : WeilCompactSmoothGV1) :
    Summable (XiMellinZeroTermV10 f.1) := by
  let e := aegisLiNontrivialZeroEquivV10
  have hA := weil_compact_smooth_zero_summable_v1 f
  have hcomp :
      Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
        XiMellinZeroTermV10 f.1 (e rho)) := by
    apply hA.congr
    intro rho
    unfold XiMellinZeroTermV10 WeilZeroIndexSummandV1
    rw [aegisLiNontrivialZeroEquivV10_val,
      xi_zeta_multiplicity_eq_v10]
  exact e.summable_iff.mp hcomp

/-- Reindexing the provider zero tsum onto the AEGIS carrier gives exactly the
canonical AEGIS zero functional. -/
theorem xi_mellin_zero_tsum_eq_aegis_v10
    (f : WeilCompactSmoothGV1) :
    (∑' rho : LiCriterion.NontrivialZero,
      XiMellinZeroTermV10 f.1 rho) =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 f.1 rho := by
  let e := aegisLiNontrivialZeroEquivV10
  calc
    (∑' rho : LiCriterion.NontrivialZero,
      XiMellinZeroTermV10 f.1 rho)
      =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        XiMellinZeroTermV10 f.1 (e rho) := by
          exact (e.tsum_eq (XiMellinZeroTermV10 f.1)).symm
    _ =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 f.1 rho := by
          apply tsum_congr
          intro rho
          unfold XiMellinZeroTermV10 WeilZeroIndexSummandV1
          rw [aegisLiNontrivialZeroEquivV10_val,
            xi_zeta_multiplicity_eq_v10]

/-- The reflected provider zero family is summable and has the same tsum as the
unreflected family. -/
theorem xi_reflected_mellin_zero_tsum_eq_v10
    (f : WeilCompactSmoothGV1) :
    (∑' rho : LiCriterion.NontrivialZero,
      (analyticOrderNatAt LiCriterion.riemannXi rho.val : ℂ) *
        mellin f.1 (1 - rho.val)) =
      ∑' rho : LiCriterion.NontrivialZero,
        XiMellinZeroTermV10 f.1 rho := by
  let P := XiMellinZeroTermV10 f.1
  calc
    (∑' rho : LiCriterion.NontrivialZero,
      (analyticOrderNatAt LiCriterion.riemannXi rho.val : ℂ) *
        mellin f.1 (1 - rho.val))
      =
      ∑' rho : LiCriterion.NontrivialZero,
        P (LiCriterion.pairedZero rho) := by
          apply tsum_congr
          intro rho
          exact
            (pairedZero_weighted_mellin_v10 f.1 rho).symm
    _ =
      ∑' rho : LiCriterion.NontrivialZero, P rho := by
          exact LiCriterion.pairedZeroEquiv.tsum_eq P

/-- The paired provider zero tsum is exactly twice the ordinary provider zero
functional. -/
theorem xi_paired_mellin_zero_tsum_eq_two_v10
    (f : WeilCompactSmoothGV1) :
    (∑' rho : LiCriterion.NontrivialZero,
      XiPairedMellinZeroTermV10 f.1 rho) =
      2 * (∑' rho : LiCriterion.NontrivialZero,
        XiMellinZeroTermV10 f.1 rho) := by
  let P := XiMellinZeroTermV10 f.1
  let R : LiCriterion.NontrivialZero → ℂ := fun rho =>
    (analyticOrderNatAt LiCriterion.riemannXi rho.val : ℂ) *
      mellin f.1 (1 - rho.val)
  have hP : Summable P := xi_mellin_zero_summable_v10 f
  have hPpair :
      Summable (fun rho : LiCriterion.NontrivialZero =>
        P (LiCriterion.pairedZero rho)) :=
    LiCriterion.pairedZeroEquiv.summable_iff.mpr hP
  have hR : Summable R := by
    apply hPpair.congr
    intro rho
    exact pairedZero_weighted_mellin_v10 f.1 rho
  have hreflect :
      (∑' rho : LiCriterion.NontrivialZero, R rho) =
        ∑' rho : LiCriterion.NontrivialZero, P rho := by
    simpa [R, P] using xi_reflected_mellin_zero_tsum_eq_v10 f
  have hadd := hP.tsum_add hR
  calc
    (∑' rho : LiCriterion.NontrivialZero,
      XiPairedMellinZeroTermV10 f.1 rho)
      =
      ∑' rho : LiCriterion.NontrivialZero, (P rho + R rho) := by
        apply tsum_congr
        intro rho
        simp [XiPairedMellinZeroTermV10, P, R,
          XiMellinZeroTermV10, mul_add]
    _ =
      (∑' rho : LiCriterion.NontrivialZero, P rho) +
        (∑' rho : LiCriterion.NontrivialZero, R rho) := hadd
    _ =
      2 * (∑' rho : LiCriterion.NontrivialZero, P rho) := by
        rw [hreflect]
        ring

/-- V5 + V9: normalized fixed-line integral of 2 ξ'/ξ against the actual
paired Mellin profile equals the paired provider zero tsum. -/
theorem normalized_two_xi_logDeriv_eq_paired_zero_tsum_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (2 * _root_.logDeriv LiCriterion.riemannXi
          ((c : ℂ) + (t : ℂ) * I)) *
            WeilPairedMellinProfileV5 f c t) =
      ∑' rho : LiCriterion.NontrivialZero,
        XiPairedMellinZeroTermV10 f.1 rho := by
  have hv5 :=
    riemannXi_paired_mellin_logDeriv_fixed_line_integral_v5 f c hc
  rw [hv5]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro rho
  have hv9 :=
    paired_zero_kernel_integral_evaluation_v9 f c hc rho
  let m : ℂ :=
    (analyticOrderNatAt LiCriterion.riemannXi rho.val : ℂ)
  calc
    (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ,
        (m * WeilPairedZeroKernelV3 c t rho) *
          WeilPairedMellinProfileV5 f c t)
      =
      m * ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          WeilPairedZeroKernelV3 c t rho *
            WeilPairedMellinProfileV5 f c t) := by
        have hfun :
            (fun t : ℝ =>
              (m * WeilPairedZeroKernelV3 c t rho) *
                WeilPairedMellinProfileV5 f c t) =
            (fun t : ℝ =>
              m * (WeilPairedZeroKernelV3 c t rho *
                WeilPairedMellinProfileV5 f c t)) := by
          funext t
          ring
        rw [hfun, integral_const_mul]
        ring
    _ =
      m * (mellin f.1 rho.val + mellin f.1 (1 - rho.val)) := by
        rw [hv9]
    _ = XiPairedMellinZeroTermV10 f.1 rho := by
        rfl

/-- Final zero-side identification on the canonical AEGIS carrier. -/
theorem normalized_two_xi_logDeriv_eq_two_aegis_zero_tsum_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (2 * _root_.logDeriv LiCriterion.riemannXi
          ((c : ℂ) + (t : ℂ) * I)) *
            WeilPairedMellinProfileV5 f c t) =
      2 * (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 f.1 rho) := by
  rw [normalized_two_xi_logDeriv_eq_paired_zero_tsum_v10 f c hc,
    xi_paired_mellin_zero_tsum_eq_two_v10 f,
    xi_mellin_zero_tsum_eq_aegis_v10 f]

end AEGIS.WeilFixedLineZeroSideV10

#print axioms AEGIS.WeilFixedLineZeroSideV10.xi_mellin_zero_tsum_eq_aegis_v10
#print axioms AEGIS.WeilFixedLineZeroSideV10.xi_paired_mellin_zero_tsum_eq_two_v10
#print axioms AEGIS.WeilFixedLineZeroSideV10.normalized_two_xi_logDeriv_eq_paired_zero_tsum_v10
#print axioms AEGIS.WeilFixedLineZeroSideV10.normalized_two_xi_logDeriv_eq_two_aegis_zero_tsum_v10
