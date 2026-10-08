import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
AEGIS Ω — multiplicity-safe nontrivial zeta-zero weight v1.

This lane establishes only pointwise zero multiplicity and a multiplicity-weighted
Mellin summand. It deliberately does not define a global sum over zeros or assert
its convergence.

ZERO_MULTIPLICITY_SAFE_POINTWISE_ONLY
GLOBAL_ZERO_SUM_OPEN
GLOBAL_ZERO_SUM_CONVERGENCE_OPEN
EXPLICIT_FORMULA_THEOREM_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex

noncomputable section

/-- Nontrivial Riemann-zeta zeros, matching the exclusions in Mathlib's RH target. -/
def RiemannNontrivialZeroIndexV1 :=
  { rho : ℂ //
      riemannZeta rho = 0 ∧
      (¬ ∃ n : ℕ, rho = -2 * (n + 1)) ∧
      rho ≠ 1 }

/-- A nontrivial zero is in Mathlib's canonical zeta-zero set. -/
theorem nontrivial_zero_mem_mathlib_zero_set_v1
    (rho : RiemannNontrivialZeroIndexV1) :
    rho.1 ∈ riemannZetaZeros :=
  mem_riemannZetaZeros.mpr rho.2.1

/-- The analytic order of zeta at a nontrivial zero is finite.

If it were `⊤`, zeta would vanish on a neighbourhood. The analytic identity
principle on the connected domain `{1}ᶜ` would then force `ζ(0)=0`, contradicting
Mathlib's theorem `riemannZeta_zero`.
-/
theorem riemannZeta_order_ne_top_at_zero_v1
    (rho : RiemannNontrivialZeroIndexV1) :
    analyticOrderAt riemannZeta rho.1 ≠ ⊤ := by
  intro htop
  have hlocal : riemannZeta =ᶠ[𝓝 rho.1] (fun _ : ℂ => 0) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    exact hz
  have hrhoU : rho.1 ∈ ({1}ᶜ : Set ℂ) := by
    simpa using rho.2.2.2
  have heq : Set.EqOn riemannZeta (fun _ : ℂ => 0) ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      hrhoU hlocal
  have hzero : riemannZeta (0 : ℂ) = 0 := by
    simpa using heq (by simp : (0 : ℂ) ∈ ({1}ᶜ : Set ℂ))
  rw [riemannZeta_zero] at hzero
  norm_num at hzero

/-- Natural multiplicity of a nontrivial zeta zero. -/
def RiemannZeroMultiplicityV1 (rho : RiemannNontrivialZeroIndexV1) : ℕ :=
  analyticOrderNatAt riemannZeta rho.1

/-- The natural multiplicity never loses a nontrivial zero to the `⊤ ↦ 0`
conversion in `analyticOrderNatAt`, and is strictly positive. -/
theorem riemann_zero_multiplicity_pos_v1
    (rho : RiemannNontrivialZeroIndexV1) :
    0 < RiemannZeroMultiplicityV1 rho := by
  have hrhoU : rho.1 ∈ ({1}ᶜ : Set ℂ) := by
    simpa using rho.2.2.2
  have hAn : AnalyticAt ℂ riemannZeta rho.1 :=
    analyticOn_riemannZeta rho.1 hrhoU
  have horder_ne0 : analyticOrderAt riemannZeta rho.1 ≠ 0 :=
    hAn.analyticOrderAt_ne_zero.mpr rho.2.1
  have horder_netop : analyticOrderAt riemannZeta rho.1 ≠ ⊤ :=
    riemannZeta_order_ne_top_at_zero_v1 rho
  apply Nat.pos_of_ne_zero
  intro hnat
  have hnat' : analyticOrderNatAt riemannZeta rho.1 = 0 := by
    simpa [RiemannZeroMultiplicityV1] using hnat
  apply horder_ne0
  calc
    analyticOrderAt riemannZeta rho.1 =
        (analyticOrderNatAt riemannZeta rho.1 : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt horder_netop).symm
    _ = 0 := by simp [hnat']

/-- Casting the recorded multiplicity back to `ℕ∞` recovers the analytic order. -/
theorem riemann_zero_multiplicity_cast_eq_order_v1
    (rho : RiemannNontrivialZeroIndexV1) :
    (RiemannZeroMultiplicityV1 rho : ℕ∞) =
      analyticOrderAt riemannZeta rho.1 := by
  unfold RiemannZeroMultiplicityV1
  exact Nat.cast_analyticOrderNatAt (riemannZeta_order_ne_top_at_zero_v1 rho)

/-- Pointwise multiplicity-weighted Mellin contribution of one nontrivial zero. -/
def WeilZeroSummandV1
    (f : ℝ → ℂ) (rho : RiemannNontrivialZeroIndexV1) : ℂ :=
  (RiemannZeroMultiplicityV1 rho : ℂ) * mellin f rho.1

#check RiemannNontrivialZeroIndexV1
#check RiemannZeroMultiplicityV1
#check riemannZeta_order_ne_top_at_zero_v1
#check riemann_zero_multiplicity_pos_v1
#check riemann_zero_multiplicity_cast_eq_order_v1
#check WeilZeroSummandV1

#print axioms nontrivial_zero_mem_mathlib_zero_set_v1
#print axioms riemannZeta_order_ne_top_at_zero_v1
#print axioms riemann_zero_multiplicity_pos_v1
#print axioms riemann_zero_multiplicity_cast_eq_order_v1
