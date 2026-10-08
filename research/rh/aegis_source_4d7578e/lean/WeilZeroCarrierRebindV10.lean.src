import ZeroCountingMellinSummabilityV1
import WeilPairedHadamardTsumFusionV1
import Mathlib.Tactic

/-!
AEGIS Ω — exact carrier rebind between the pinned Li-criterion nontrivial-zero
subtype and the repository's canonical zeta nontrivial-zero subtype.

Both carriers represent the same mathematical zeros:
* LiCriterion.NontrivialZero: zeta zero with 0 < Re rho < 1;
* RiemannNontrivialZeroIndexV2: zeta zero excluding negative even integers.

The critical-strip theorem supplies AEGIS -> Li; positivity of the real part
supplies Li -> AEGIS.  Multiplicity equality is inherited from
`li_xi_zeta_multiplicity_eq_v1`.

AUTHORITY_EFFECT = NONE.
-/

open Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilZeroCarrierRebindV10

/-- Canonical map from the Li-criterion carrier into the AEGIS zeta-zero
carrier. -/
def liZeroToAegisV10 :
    LiCriterion.NontrivialZero → RiemannNontrivialZeroIndexV2 :=
  fun rho => ⟨rho.1, rho.2.1, by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have hrho : 0 < rho.1.re := rho.2.2.1
    simp at hre
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith⟩

/-- Canonical map from the AEGIS carrier into the Li-criterion carrier. -/
def aegisZeroToLiV10 :
    RiemannNontrivialZeroIndexV2 → LiCriterion.NontrivialZero :=
  fun rho => by
    have hstrip :=
      riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
    exact ⟨rho.1, rho.2.1, hstrip.1, hstrip.2⟩

@[simp] theorem liZeroToAegis_val_v10
    (rho : LiCriterion.NontrivialZero) :
    (liZeroToAegisV10 rho).1 = rho.1 := rfl

@[simp] theorem aegisZeroToLi_val_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    (aegisZeroToLiV10 rho).1 = rho.1 := rfl

theorem liZeroToAegis_left_inv_v10
    (rho : LiCriterion.NontrivialZero) :
    aegisZeroToLiV10 (liZeroToAegisV10 rho) = rho := by
  apply Subtype.ext
  rfl

theorem aegisZeroToLi_left_inv_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    liZeroToAegisV10 (aegisZeroToLiV10 rho) = rho := by
  apply Subtype.ext
  rfl

/-- Exact equivalence of the two nontrivial-zero carriers. -/
def zeroCarrierEquivV10 :
    LiCriterion.NontrivialZero ≃ RiemannNontrivialZeroIndexV2 where
  toFun := liZeroToAegisV10
  invFun := aegisZeroToLiV10
  left_inv := liZeroToAegis_left_inv_v10
  right_inv := aegisZeroToLi_left_inv_v10

/-- Analytic multiplicity is preserved by the carrier equivalence. -/
theorem zeroCarrierEquiv_multiplicity_v10
    (rho : LiCriterion.NontrivialZero) :
    analyticOrderNatAt LiCriterion.riemannXi rho.1 =
      analyticOrderNatAt riemannZeta (zeroCarrierEquivV10 rho).1 := by
  simpa [zeroCarrierEquivV10] using li_xi_zeta_multiplicity_eq_v1 rho

/-- One multiplicity-weighted Mellin summand is literally the canonical AEGIS
zero summand after reindexing. -/
theorem zeroCarrierEquiv_summand_v10
    (f : ℝ → ℂ) (rho : LiCriterion.NontrivialZero) :
    (analyticOrderNatAt LiCriterion.riemannXi rho.1 : ℂ) *
        mellin f rho.1 =
      WeilZeroIndexSummandV1 f (zeroCarrierEquivV10 rho) := by
  unfold WeilZeroIndexSummandV1
  rw [← zeroCarrierEquiv_multiplicity_v10 rho]
  rfl

/-- Reindexing the multiplicity-weighted xi Mellin tsum gives exactly the
canonical AEGIS zeta-zero tsum. -/
theorem xi_mellin_tsum_eq_aegis_zero_tsum_v10
    (f : ℝ → ℂ) :
    (∑' rho : LiCriterion.NontrivialZero,
      (analyticOrderNatAt LiCriterion.riemannXi rho.1 : ℂ) *
        mellin f rho.1) =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 f rho := by
  calc
    (∑' rho : LiCriterion.NontrivialZero,
      (analyticOrderNatAt LiCriterion.riemannXi rho.1 : ℂ) *
        mellin f rho.1)
      =
      ∑' rho : LiCriterion.NontrivialZero,
        WeilZeroIndexSummandV1 f (zeroCarrierEquivV10 rho) := by
          apply tsum_congr
          intro rho
          exact zeroCarrierEquiv_summand_v10 f rho
    _ =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 f rho := by
          simpa using
            (Equiv.tsum_eq zeroCarrierEquivV10
              (fun rho : RiemannNontrivialZeroIndexV2 =>
                WeilZeroIndexSummandV1 f rho)).symm

end AEGIS.WeilZeroCarrierRebindV10

#print axioms AEGIS.WeilZeroCarrierRebindV10.zeroCarrierEquiv_multiplicity_v10
#print axioms AEGIS.WeilZeroCarrierRebindV10.xi_mellin_tsum_eq_aegis_zero_tsum_v10
