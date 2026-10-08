import RHRestrictedWeilBridgeV13
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
AEGIS Ω — globalization chain to RH, V13.

Lean counterpart of `formal/theories/Weil/Globalization.v`
(`globalization_ready_implies_global_weil_positivity_v1`), wired to the
kernel-checked `final_sign_implies_rh_v13 : FinalSignResidualV1 → RiemannHypothesis`.
The earlier held assembly (`WeilChainAssemblyV1`) carried the Weil criterion as an
explicit `criterion` hypothesis; that hypothesis is now discharged by V13.

What remains as hypotheses is exactly the arithmetic sign on an exhausting family of
packet classes `S n` (e.g. support width ≤ L_n with L_n → ∞), optionally with an error
`ε n → 0`.  `uniform_lower_bound_collapses` records why the error buys nothing for a
quadratic form under scaling: a uniform lower bound `-ε` already forces `0`.

No RH claim is made: the sign hypotheses are not proved here.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGlobalizationChainV13

open Filter Topology
open AEGIS.RHFinalClosureV1
open AEGIS.RHRestrictedWeilBridgeV13

/-- The globalization step (Coq `GlobalizationReadyV1`): pointwise convergence, a
vanishing error and a lower bound by that error give nonnegativity of the limit. -/
theorem globalization_limit_nonneg
    {α : Type*} (Q : ℕ → α → ℝ) (Qlim : α → ℝ) (eps : ℕ → ℝ)
    (hconv : ∀ f, Tendsto (fun n => Q n f) atTop (𝓝 (Qlim f)))
    (heps : Tendsto eps atTop (𝓝 0))
    (hbound : ∀ n f, -(eps n) ≤ Q n f) :
    ∀ f, 0 ≤ Qlim f := by
  intro f
  have hneg : Tendsto (fun n => -(eps n)) atTop (𝓝 0) := by
    simpa using heps.neg
  exact le_of_tendsto_of_tendsto' hneg (hconv f) (fun n => hbound n f)

/-- CONTROL: the vanishing of the error is load-bearing. -/
theorem vanishing_error_is_indispensable :
    ¬ (∀ (Q : ℕ → Unit → ℝ) (Qlim : Unit → ℝ) (eps : ℕ → ℝ),
        (∀ f, Tendsto (fun n => Q n f) atTop (𝓝 (Qlim f))) →
        (∀ n, 0 ≤ eps n) →
        (∀ n f, -(eps n) ≤ Q n f) →
        ∀ f, 0 ≤ Qlim f) := by
  intro h
  have := h (fun _ _ => -1) (fun _ => -1) (fun _ => 1)
    (fun _ => tendsto_const_nhds) (fun _ => zero_le_one)
    (fun _ _ => le_refl _) ()
  norm_num at this

/-- For a quadratic form (degree-2 homogeneous under real scaling) a uniform lower
bound `-ε` already forces nonnegativity: the error term of a globalization buys
nothing over exact positivity. -/
theorem uniform_lower_bound_collapses
    {α : Type*} (Q : α → ℝ) (smul : ℝ → α → α)
    (hhom : ∀ t f, Q (smul t f) = t ^ 2 * Q f)
    (ε : ℝ) (hb : ∀ f, -ε ≤ Q f) :
    ∀ f, 0 ≤ Q f := by
  intro f
  by_contra hneg
  push_neg at hneg
  set c : ℝ := (|ε| + 1) / (-Q f) with hc
  have hpos : 0 < -Q f := by linarith
  have hc0 : 0 ≤ c := div_nonneg (by positivity) hpos.le
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hne : Q f ≠ 0 := ne_of_lt hneg
  have key : Q (smul (Real.sqrt c) f) = -(|ε| + 1) := by
    rw [hhom, hsq, hc, div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hne]
    ring
  have := hb (smul (Real.sqrt c) f)
  rw [key] at this
  have := le_abs_self ε
  linarith

/-- RH from the arithmetic sign on every class of an exhausting family. -/
theorem rh_of_sign_on_exhaustion
    (S : ℕ → WeilCompactSmoothGV1 → Prop)
    (hcover : ∀ g, ∃ n, S n g)
    (hsign : ∀ n g, S n g → WeilMomentConditionsV1 g →
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0) :
    RiemannHypothesis :=
  final_sign_implies_rh_v13 (fun g hm =>
    let ⟨n, hn⟩ := hcover g
    hsign n g hn hm)

/-- Globalized form: an increasing exhausting family on which the sign holds up to an
error `ε n → 0` already gives RH. -/
theorem rh_of_vanishing_error_on_exhaustion
    (S : ℕ → WeilCompactSmoothGV1 → Prop)
    (hmono : ∀ n m g, n ≤ m → S n g → S m g)
    (hcover : ∀ g, ∃ n, S n g)
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0))
    (hsign : ∀ n g, S n g → WeilMomentConditionsV1 g →
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ eps n) :
    RiemannHypothesis := by
  refine final_sign_implies_rh_v13 (fun g hm => ?_)
  obtain ⟨n, hn⟩ := hcover g
  have hev : ∀ᶠ m in atTop,
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ eps m :=
    eventually_atTop.2 ⟨n, fun m hm' => hsign m g (hmono n m g hm' hn) hm⟩
  exact ge_of_tendsto heps hev

end AEGIS.RHGlobalizationChainV13

open AEGIS.RHGlobalizationChainV13 in
#print axioms globalization_limit_nonneg
open AEGIS.RHGlobalizationChainV13 in
#print axioms vanishing_error_is_indispensable
open AEGIS.RHGlobalizationChainV13 in
#print axioms uniform_lower_bound_collapses
open AEGIS.RHGlobalizationChainV13 in
#print axioms rh_of_sign_on_exhaustion
open AEGIS.RHGlobalizationChainV13 in
#print axioms rh_of_vanishing_error_on_exhaustion
