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

import RHDyadicTowerV13
import RHRestrictedWeilBridgeV13
import Mathlib.Topology.Order.Basic

/-!
# Closure of the actual Weil form along certified packet approximations

The packet certificates below consume `RHDyadicTowerV13.tower_arithmetic_nonpositive`.
Convergence is convergence of the actual arithmetic form, not convergence of shift
locations or an unspecified function norm. The criterion uses
`RHRestrictedWeilBridgeV13.restricted_weil_criterion_kernel_bridge_v13`.
-/

open Filter Topology Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCertifiedApproximationV1

open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHDyadicTowerV13
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHMillenniumGateV10
open AEGIS.RHRestrictedWeilBridgeV13

/-- The actual arithmetic side of the repository autocorrelation form. -/
def arithmeticValue (g : WeilCompactSmoothGV1) : ℝ :=
  (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re

/-- A packet with all hypotheses of the existing dyadic positivity producer. -/
def DyadicCertified (p : WeilCompactSmoothGV1) : Prop :=
  ∃ (N m : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (z : Fin (N + 1) → ℂ),
    10 ≤ m ∧ N + 2 ≤ m ∧ HalfWidthAt g (hw m) a ∧
      WeilMomentConditionsV1 g ∧ p = towerPacket N g z

/-- The certificate proves the required sign for the actual form. -/
theorem dyadicCertified_nonpositive (p : WeilCompactSmoothGV1)
    (hp : DyadicCertified p) : arithmeticValue p ≤ 0 := by
  rcases hp with ⟨N, m, g, a, z, hm10, hmN, hwg, hmom, rfl⟩
  exact tower_arithmetic_nonpositive N m hm10 hmN g a hwg hmom z

/-- Nonpositivity is closed under convergence of the actual arithmetic values. -/
theorem arithmetic_nonpositive_of_certified_limit
    (C : WeilCompactSmoothGV1 → Prop)
    (hC : ∀ p, C p → arithmeticValue p ≤ 0)
    (g : WeilCompactSmoothGV1) (p : ℕ → WeilCompactSmoothGV1)
    (hp : ∀ n, C (p n))
    (hlim : Tendsto (fun n => arithmeticValue (p n)) atTop (𝓝 (arithmeticValue g))) :
    arithmeticValue g ≤ 0 := by
  exact isClosed_Iic.mem_of_tendsto hlim (Eventually.of_forall fun n => hC (p n) (hp n))

/-- A precise scalar-form approximation obligation for the existing dyadic class. -/
def DyadicArithmeticApproximationV1 : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    ∃ p : ℕ → WeilCompactSmoothGV1,
      (∀ n, DyadicCertified (p n)) ∧
      Tendsto (fun n => arithmeticValue (p n)) atTop (𝓝 (arithmeticValue g))

/-- Certified approximation supplies the exact unconditional gate proposition. -/
theorem universal_of_dyadic_arithmetic_approximation
    (happrox : DyadicArithmeticApproximationV1) :
    UniversalZeroQuadraticNonnegativeV10 := by
  intro g hm
  obtain ⟨p, hp, hlim⟩ := happrox g hm
  have hnonpos := arithmetic_nonpositive_of_certified_limit DyadicCertified
    dyadicCertified_nonpositive g p hp hlim
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp hnonpos

/-- The existing kernel criterion maps this precise approximation obligation to Mathlib RH. -/
theorem riemannHypothesis_of_dyadic_arithmetic_approximation
    (happrox : DyadicArithmeticApproximationV1) : RiemannHypothesis :=
  restricted_weil_criterion_kernel_bridge_v13
    (universal_of_dyadic_arithmetic_approximation happrox)

#print axioms AEGIS.RHCertifiedApproximationV1.dyadicCertified_nonpositive
#print axioms AEGIS.RHCertifiedApproximationV1.arithmetic_nonpositive_of_certified_limit
#print axioms AEGIS.RHCertifiedApproximationV1.universal_of_dyadic_arithmetic_approximation
#print axioms AEGIS.RHCertifiedApproximationV1.riemannHypothesis_of_dyadic_arithmetic_approximation

end AEGIS.RHCertifiedApproximationV1
