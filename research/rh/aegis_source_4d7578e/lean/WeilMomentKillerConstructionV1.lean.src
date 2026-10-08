/-
AEGIS Ω — the moment-killing operator φ = ψ' + ψ'', V1.

`WeilArchimedeanPacketWitnessV1` supplies a packet with the right log-support
but records, as an honest negative, that the bump packet does NOT satisfy
`WeilMomentConditionsV1`: a nonneg bump has strictly positive integral.  The
same file records the intended repair as a *plan*:

    take φ = ψ' + ψ'' for any smooth compactly supported ψ; then
    ∫_ℝ φ = 0 and ∫_ℝ φ(u) e^u du = 0, with supp φ ⊆ supp ψ.

This module proves that plan.  It proves nothing else.

THE MECHANISM

Both moments die for the same reason, and the reason is one lemma
(`integral_deriv_eq_zero`): a C¹ compactly supported function integrates its
derivative to zero over ℝ.  The two applications are

    φ        = deriv (ψ + ψ')              — compactly supported
    φ · exp  = deriv (ψ' · exp)            — compactly supported

both verified pointwise by `HasDerivAt.add` / `HasDerivAt.mul`.  No integration
by parts is invoked; the antiderivatives are exhibited, which is strictly
cheaper and leaves no boundary term to argue about.  In particular ψ' · exp is compactly
supported even though exp is not, because ψ' is.

NON-TRIVIALITY

`eq_zero_of_momentKiller_eq_zero` is the control that keeps the construction
from being vacuous: φ ≡ 0 forces ψ ≡ 0.  The argument is the ODE one recorded
in the plan, run backwards through the same two antiderivatives — ψ + ψ' is
constant and compactly supported hence 0, so ψ' = -ψ, so ψ·exp is constant and
compactly supported hence 0, so ψ = 0.

`psi0` / `phi0` instantiate this at a bump centred at 0 in the log coordinate
with outer radius 1/40, giving a concrete nonzero φ whose support sits inside
the certificate window [-1/32, 1/32].  Note this bump lives in u-space, where
the window is an interval about 0; the bump of `WeilArchimedeanPacketWitnessV1`
lives in x-space, centred at 1.  They are different objects, related by
x = e^u, and this file does not assert that relation.

A CONSEQUENCE WORTH RECORDING

`phi0_not_nonneg` is proved, not assumed: a continuous compactly supported
function with vanishing integral that is not identically zero must take
negative values.  So the moment-killing operator necessarily destroys any
pointwise nonnegativity of the packet.  Whatever discharges
`ArchimedeanPacketReductionV1` downstream cannot lean on the packet being
nonneg; it has to come from the autocorrelation, which is a different object.

WHAT THIS IS NOT

This does **not** discharge `WeilMomentConditionsV1` for a multiplicative
packet.  That statement is about ∫_{Ioi 0} g(x) dx/x and ∫_{Ioi 0} g(x) dx for
g : ℝ → ℂ, and getting there from the two integrals proved here needs the
change of variables x = e^u — step (ii) of `WeilArchimedeanPacketWitnessV1`,
which is still OPEN.  Nothing here performs that change of variables, and
nothing here mentions g.

`ANALYTIC_DIAGONAL_LOWER_V1`, step (iii) (autocorrelation vanishing outside the
log-support), the global Weil sign and RH all remain OPEN.  This module proves
no sign and no part of RH.
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

open MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace AEGIS.WeilMomentKillerConstructionV1

/-! ### The one lemma both moments reduce to -/

/-- A C¹ function with compact support integrates its derivative to zero over
all of ℝ.  Split at 0 and use Mathlib's two half-line statements, whose
boundary values at 0 cancel. -/
theorem integral_deriv_eq_zero {G : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) :
    ∫ u : ℝ, deriv G u = 0 := by
  have hint : Integrable (deriv G) :=
    (hG.continuous_deriv le_rfl).integrable_of_hasCompactSupport hGc.deriv
  have h := intervalIntegral.integral_Iic_add_Ioi (f := deriv G) (b := (0 : ℝ))
    hint.integrableOn hint.integrableOn
  rw [HasCompactSupport.integral_Iic_deriv_eq hG hGc 0,
    HasCompactSupport.integral_Ioi_deriv_eq hG hGc 0] at h
  linarith

/-- A constant function with compact support on ℝ is zero: the cocompact filter
is nontrivial, so some point already sees the value 0. -/
theorem eq_zero_of_const_of_hasCompactSupport {F : ℝ → ℝ}
    (hFc : HasCompactSupport F) (hconst : ∀ x y : ℝ, F x = F y) : ∀ x, F x = 0 := by
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hFc
  obtain ⟨y, hy⟩ := hFc.exists
  intro x
  rw [hconst x y]
  simpa using hy

/-! ### The operator -/

/-- `φ = ψ' + ψ''`. -/
def momentKiller (ψ : ℝ → ℝ) : ℝ → ℝ := fun u => deriv ψ u + deriv (deriv ψ) u

section Smooth

variable {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)

include hψ

theorem contDiff_deriv : ContDiff ℝ ∞ (deriv ψ) :=
  (contDiff_infty_iff_deriv.mp hψ).2

theorem differentiable_self : Differentiable ℝ ψ := hψ.differentiable (by simp)

theorem differentiable_deriv : Differentiable ℝ (deriv ψ) :=
  (contDiff_deriv hψ).differentiable (by simp)

/-- The first antiderivative: `φ = (ψ + ψ')'`. -/
theorem momentKiller_eq_deriv :
    momentKiller ψ = deriv (fun u => ψ u + deriv ψ u) := by
  funext u
  have hd : HasDerivAt (fun u => ψ u + deriv ψ u)
      (deriv ψ u + deriv (deriv ψ) u) u :=
    ((differentiable_self hψ u).hasDerivAt).add ((differentiable_deriv hψ u).hasDerivAt)
  rw [hd.deriv]
  rfl

/-- The second antiderivative: `φ · exp = (ψ' · exp)'`.  This is where the
`e^u` weight is absorbed. -/
theorem momentKiller_mul_exp_eq_deriv :
    (fun u => momentKiller ψ u * Real.exp u)
      = deriv (fun u => deriv ψ u * Real.exp u) := by
  funext u
  have hd : HasDerivAt (fun u => deriv ψ u * Real.exp u)
      (deriv (deriv ψ) u * Real.exp u + deriv ψ u * Real.exp u) u :=
    ((differentiable_deriv hψ u).hasDerivAt).mul (Real.hasDerivAt_exp u)
  rw [hd.deriv]
  simp only [momentKiller]
  ring

theorem momentKiller_contDiff : ContDiff ℝ ∞ (momentKiller ψ) :=
  (contDiff_deriv hψ).add (contDiff_deriv (contDiff_deriv hψ))

section Compact

variable (hc : HasCompactSupport ψ)

include hc

omit hψ in
theorem momentKiller_hasCompactSupport : HasCompactSupport (momentKiller ψ) :=
  hc.deriv.add hc.deriv.deriv

/-- **First moment.**  `∫_ℝ φ = 0` — in the log coordinate this is the
`dx/x` moment. -/
theorem integral_momentKiller : ∫ u : ℝ, momentKiller ψ u = 0 := by
  rw [momentKiller_eq_deriv hψ]
  refine integral_deriv_eq_zero ?_ (hc.add hc.deriv)
  exact (hψ.of_le (by simp)).add ((contDiff_deriv hψ).of_le (by simp))

/-- **Second moment.**  `∫_ℝ φ(u) e^u du = 0` — in the log coordinate this is
the `dx` moment. -/
theorem integral_momentKiller_mul_exp :
    ∫ u : ℝ, momentKiller ψ u * Real.exp u = 0 := by
  have hrw : ∫ u : ℝ, momentKiller ψ u * Real.exp u
      = ∫ u : ℝ, deriv (fun v => deriv ψ v * Real.exp v) u := by
    rw [momentKiller_mul_exp_eq_deriv hψ]
  rw [hrw]
  refine integral_deriv_eq_zero ?_ hc.deriv.mul_right
  exact ((contDiff_deriv hψ).of_le (by simp)).mul (Real.contDiff_exp.of_le le_top)

/-- **Non-vacuity.**  If the operator kills ψ entirely then ψ was already zero,
so a nonzero ψ gives a nonzero φ.  Both steps are the same trick as the two
moments, read backwards. -/
theorem eq_zero_of_momentKiller_eq_zero (h : momentKiller ψ = 0) : ∀ x, ψ x = 0 := by
  -- ψ + ψ' is constant (its derivative is φ) and compactly supported, hence 0.
  have hsum : ∀ x, ψ x + deriv ψ x = 0 := by
    refine eq_zero_of_const_of_hasCompactSupport (hc.add hc.deriv) ?_
    refine is_const_of_deriv_eq_zero
      ((differentiable_self hψ).add (differentiable_deriv hψ)) ?_
    intro x
    rw [← momentKiller_eq_deriv hψ, h]
    rfl
  -- hence ψ' = -ψ, so ψ · exp has zero derivative.
  have hK : ∀ x, ψ x * Real.exp x = 0 := by
    refine eq_zero_of_const_of_hasCompactSupport hc.mul_right ?_
    refine is_const_of_deriv_eq_zero
      ((differentiable_self hψ).mul Real.differentiable_exp) ?_
    intro x
    have hd : HasDerivAt (fun y => ψ y * Real.exp y)
        (deriv ψ x * Real.exp x + ψ x * Real.exp x) x :=
      ((differentiable_self hψ x).hasDerivAt).mul (Real.hasDerivAt_exp x)
    rw [hd.deriv]
    linear_combination (Real.exp x) * hsum x
  intro x
  have := hK x
  have hx := Real.exp_pos x
  nlinarith

end Compact

end Smooth

/-! ### A concrete nonzero witness inside the window -/

/-- A bump in the LOG coordinate, centred at 0 with outer radius 1/40.  This is
not the x-space bump of `WeilArchimedeanPacketWitnessV1`. -/
def ubump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 80
  rOut := 1 / 40
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The seed. -/
def psi0 : ℝ → ℝ := fun u => ubump u

/-- The moment-killed packet in the log coordinate. -/
def phi0 : ℝ → ℝ := momentKiller psi0

theorem psi0_contDiff : ContDiff ℝ ∞ psi0 := ubump.contDiff

theorem psi0_tsupport : tsupport psi0 = closedBall (0 : ℝ) (1 / 40) := by
  show tsupport (ubump : ℝ → ℝ) = _
  rw [ubump.tsupport_eq]
  norm_num [ubump]

theorem psi0_hasCompactSupport : HasCompactSupport psi0 := by
  rw [HasCompactSupport, psi0_tsupport]
  exact isCompact_closedBall _ _

theorem psi0_ne_zero : psi0 0 = 1 :=
  ubump.one_of_mem_closedBall (by simp [Metric.mem_closedBall, ubump])

/-- Support is not enlarged: `supp φ ⊆ supp ψ`, twice through
`tsupport_deriv_subset`. -/
theorem tsupport_momentKiller_subset (ψ : ℝ → ℝ) :
    tsupport (momentKiller ψ) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro u hu
  by_contra hnot
  refine hu ?_
  have h1 : deriv ψ u = 0 := by
    by_contra h
    exact hnot (support_deriv_subset (by simpa [Function.mem_support] using h))
  have h2 : deriv (deriv ψ) u = 0 := by
    by_contra h
    exact hnot (tsupport_deriv_subset
      (support_deriv_subset (by simpa [Function.mem_support] using h)))
  simp [momentKiller, h1, h2]

/-- **The window control.**  `phi0` lives inside the certificate's width-1/32
window in the log coordinate. -/
theorem phi0_log_support : tsupport phi0 ⊆ Icc (-(1 / 32) : ℝ) (1 / 32) := by
  refine (tsupport_momentKiller_subset psi0).trans ?_
  rw [psi0_tsupport, Real.closedBall_eq_Icc]
  exact Icc_subset_Icc (by norm_num) (by norm_num)

/-- **Both moments vanish** for the concrete witness. -/
theorem phi0_moments :
    (∫ u : ℝ, phi0 u) = 0 ∧ (∫ u : ℝ, phi0 u * Real.exp u) = 0 :=
  ⟨integral_momentKiller psi0_contDiff psi0_hasCompactSupport,
    integral_momentKiller_mul_exp psi0_contDiff psi0_hasCompactSupport⟩

/-- CONTROL (non-vacuity): the witness is not the zero function, so the two
vanishing moments above are not vacuous. -/
theorem phi0_ne_zero : phi0 ≠ 0 := by
  intro h
  have := eq_zero_of_momentKiller_eq_zero psi0_contDiff psi0_hasCompactSupport h 0
  rw [psi0_ne_zero] at this
  norm_num at this

/-- CONTROL (the honest negative): `phi0` is NOT nonnegative.  A function with
vanishing integral that is not identically zero must change sign, so no
positivity of the packet itself survives this construction. -/
theorem phi0_not_nonneg : ¬ (∀ u : ℝ, 0 ≤ phi0 u) := by
  intro hnn
  have hint : ∫ u : ℝ, phi0 u = 0 := phi0_moments.1
  have hcs : HasCompactSupport phi0 :=
    momentKiller_hasCompactSupport psi0_hasCompactSupport
  have hcont : Continuous phi0 :=
    (momentKiller_contDiff psi0_contDiff).continuous
  have hae : phi0 =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn
      (hcont.integrable_of_hasCompactSupport hcs)).mp hint
  exact phi0_ne_zero ((hcont.ae_eq_iff_eq volume continuous_zero).mp hae)

end AEGIS.WeilMomentKillerConstructionV1

#print axioms AEGIS.WeilMomentKillerConstructionV1.integral_deriv_eq_zero
#print axioms AEGIS.WeilMomentKillerConstructionV1.momentKiller_eq_deriv
#print axioms AEGIS.WeilMomentKillerConstructionV1.momentKiller_mul_exp_eq_deriv
#print axioms AEGIS.WeilMomentKillerConstructionV1.integral_momentKiller
#print axioms AEGIS.WeilMomentKillerConstructionV1.integral_momentKiller_mul_exp
#print axioms AEGIS.WeilMomentKillerConstructionV1.eq_zero_of_momentKiller_eq_zero
#print axioms AEGIS.WeilMomentKillerConstructionV1.tsupport_momentKiller_subset
#print axioms AEGIS.WeilMomentKillerConstructionV1.phi0_log_support
#print axioms AEGIS.WeilMomentKillerConstructionV1.phi0_moments
#print axioms AEGIS.WeilMomentKillerConstructionV1.phi0_ne_zero
#print axioms AEGIS.WeilMomentKillerConstructionV1.phi0_not_nonneg
