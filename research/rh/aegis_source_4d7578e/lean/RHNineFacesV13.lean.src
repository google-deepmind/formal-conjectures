import WeilRHImpliesFinalSignV13
import WeilWindowExhaustionV1
import RHTranslatedKernelDominanceV1
import RHFinalClosureSpineV1
import Mathlib.Tactic

/-!
AEGIS Ω — the nine faces of RH in this repository, V13.

Every RH-equivalent proposition that exists on any branch, proved equivalent
to Mathlib's `RiemannHypothesis` in one kernel-checked statement.  Nine names,
one proposition.  The file then asks the kernel for the proposition itself.

AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNineFacesV13

open AEGIS.RHFinalClosureV1
open AEGIS.RHMillenniumGateV10
open AEGIS.WeilRHImpliesFinalSignV13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.RHTranslatedKernelDominanceV1
open AEGIS.RHRestrictedWeilBridgeV13

theorem rh_iff_weil_negativity_v13 :
    RiemannHypothesis ↔ WeilCompactSmoothNegativityV1 :=
  rh_iff_final_sign_v13.trans final_sign_residual_iff_weil_negativity_v1

theorem rh_iff_universal_arithmetic_v13 :
    RiemannHypothesis ↔ UniversalArithmeticNonpositiveV1 :=
  rh_iff_weil_negativity_v13.trans
    weil_compact_smooth_negativity_iff_unconditional_real_inequality_v1

theorem rh_iff_all_windows_v13 :
    RiemannHypothesis ↔ ∀ L : ℝ, 0 < L → WindowArithmeticNonpositiveV1 L :=
  rh_iff_weil_negativity_v13.trans weil_compact_smooth_negativity_iff_all_windows_v1

theorem rh_iff_nat_windows_v13 :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 < n → WindowArithmeticNonpositiveV1 (n : ℝ) :=
  rh_iff_weil_negativity_v13.trans weil_compact_smooth_negativity_iff_positive_nat_windows_v1

theorem rh_iff_zero_shift_dominance_v13 :
    RiemannHypothesis ↔ ZeroShiftComponentDominanceV1 :=
  rh_iff_final_sign_v13.trans zero_shift_component_dominance_iff_final_sign_v1.symm

theorem rh_iff_certificate_v13 :
    RiemannHypothesis ↔ RHMillenniumCertificateV10 :=
  ⟨fun h => ⟨rh_implies_universal_v13 h, restricted_weil_criterion_kernel_bridge_v13⟩,
   millennium_certificate_proves_mathlib_rh_v10⟩

/-- Nine names for one proposition, all kernel-checked. -/
theorem nine_faces_of_rh_v13 :
    (RiemannHypothesis ↔ FinalSignResidualV1) ∧
    (RiemannHypothesis ↔ UniversalZeroQuadraticNonnegativeV10) ∧
    (RiemannHypothesis ↔ MillenniumMomentReachedV10) ∧
    (RiemannHypothesis ↔ RHMillenniumCertificateV10) ∧
    (RiemannHypothesis ↔ WeilCompactSmoothNegativityV1) ∧
    (RiemannHypothesis ↔ UniversalArithmeticNonpositiveV1) ∧
    (RiemannHypothesis ↔ ZeroShiftComponentDominanceV1) ∧
    (RiemannHypothesis ↔ ∀ L : ℝ, 0 < L → WindowArithmeticNonpositiveV1 L) ∧
    (RiemannHypothesis ↔ ∀ n : ℕ, 0 < n → WindowArithmeticNonpositiveV1 (n : ℝ)) :=
  ⟨rh_iff_final_sign_v13, rh_iff_universal_v13, millennium_moment_iff_rh_v13.symm,
   rh_iff_certificate_v13, rh_iff_weil_negativity_v13, rh_iff_universal_arithmetic_v13,
   rh_iff_zero_shift_dominance_v13, rh_iff_all_windows_v13, rh_iff_nat_windows_v13⟩

end AEGIS.RHNineFacesV13

#print axioms AEGIS.RHNineFacesV13.nine_faces_of_rh_v13
