import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic
import WeilMomentKillerConstructionV1

/-!
AEGIS Ω — canonical log-transport adapter v1.

Mechanical extraction of the already-proved generic transport and guarded
multiplicative-packet lemmas from WeilLogChangeOfVariablesV1.

The legacy source subsequently restated WeilCompactSmoothGV1 and
WeilMomentConditionsV1 for a standalone build.  Those restatements are
intentionally excluded here.  This module introduces no RH-domain definition.
-/

open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace AEGIS.WeilLogTransportCanonicalV1

open AEGIS.WeilMomentKillerConstructionV1

/-! ### Extending Mathlib's `Ioi a` change of variables to the whole half-line -/

/-- If the integrand vanishes on `Ioc 0 c` then the `Ioi 0` integral is already
the `Ioi c` integral.  This is what lets Mathlib's `a > 0` change of variables
reach down to `0`. -/
theorem integral_Ioi_zero_eq_Ioi {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hvan : ∀ x ∈ Ioc (0 : ℝ) c, f x = 0) (hi : IntegrableOn f (Ioi c)) :
    ∫ x in Ioi (0 : ℝ), f x = ∫ x in Ioi c, f x := by
  have hzero : IntegrableOn f (Ioc (0 : ℝ) c) :=
    integrableOn_zero.congr_fun (fun x hx => (hvan x hx).symm) measurableSet_Ioc
  rw [← Set.Ioc_union_Ioi_eq_Ioi hc.le,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hzero hi,
    setIntegral_eq_zero_of_forall_eq_zero hvan, zero_add]

/-- If the integrand vanishes on `Iic b` then the `Ioi b` integral is the whole
line integral. -/
theorem integral_Ioi_eq_integral {f : ℝ → ℝ} {b : ℝ}
    (hvan : ∀ x ∈ Iic b, f x = 0) (hi : Integrable f) :
    ∫ x in Ioi b, f x = ∫ x : ℝ, f x := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (f := f) (b := b)
    hi.integrableOn hi.integrableOn, setIntegral_eq_zero_of_forall_eq_zero hvan, zero_add]

/-! ### The two transported moments -/

section Transport

variable {φ : ℝ → ℝ} {b B : ℝ}

/-- Vanishing on both tails gives compact support outright. -/
theorem hasCompactSupport_of_tails (hb : ∀ u ≤ b, φ u = 0) (hB : ∀ u, B ≤ u → φ u = 0) :
    HasCompactSupport φ := by
  refine HasCompactSupport.intro (isCompact_Icc (a := b) (b := B)) ?_
  intro x hx
  rcases not_and_or.mp (fun h => hx ⟨h.1, h.2⟩) with h | h
  · exact hb x (le_of_not_ge h)
  · exact hB x (le_of_not_ge h)

variable (hφ : Continuous φ) (hb : ∀ u ≤ b, φ u = 0) (hB : ∀ u, B ≤ u → φ u = 0)

include hφ hb hB

theorem integrable_of_tails : Integrable φ :=
  hφ.integrable_of_hasCompactSupport (hasCompactSupport_of_tails hb hB)

omit hφ hB in
/-- The multiplicative integrand vanishes below `exp b`. -/
theorem comp_log_vanishes : ∀ x ∈ Ioc (0 : ℝ) (Real.exp b), φ (Real.log x) = 0 := by
  intro x hx
  refine hb _ ?_
  have := (Real.log_le_log_iff hx.1 (Real.exp_pos b)).2 hx.2
  rwa [Real.log_exp] at this

/-- **The `dx/x` moment transports.** -/
theorem integral_inv_mul_comp_log :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * φ (Real.log x) = ∫ u : ℝ, φ u := by
  have hint : Integrable φ := integrable_of_tails hφ hb hB
  have hc : (0 : ℝ) < Real.exp b := Real.exp_pos b
  have hIO : IntegrableOn (fun x : ℝ => x⁻¹ * φ (Real.log x)) (Ioi (Real.exp b)) := by
    have := (integrableOn_comp_log_Ioi (φ) (a := Real.exp b) hc).2
      (by rw [Real.log_exp]; exact hint.integrableOn)
    simpa [smul_eq_mul] using this
  have hstep1 : ∫ x in Ioi (0 : ℝ), x⁻¹ * φ (Real.log x)
      = ∫ x in Ioi (Real.exp b), x⁻¹ * φ (Real.log x) :=
    integral_Ioi_zero_eq_Ioi hc
      (fun x hx => by rw [comp_log_vanishes hb x hx, mul_zero]) hIO
  have hstep2 : ∫ x in Ioi (Real.exp b), x⁻¹ * φ (Real.log x) = ∫ y in Ioi b, φ y := by
    have := integral_comp_log_Ioi (φ) (a := Real.exp b) hc
    rw [Real.log_exp] at this
    simpa [smul_eq_mul] using this
  rw [hstep1, hstep2]
  exact integral_Ioi_eq_integral (fun x hx => hb x hx) hint

/-- **The `dx` moment transports**, picking up the `e^u` weight. -/
theorem integral_comp_log :
    ∫ x in Ioi (0 : ℝ), φ (Real.log x) = ∫ u : ℝ, φ u * Real.exp u := by
  have hint : Integrable φ := integrable_of_tails hφ hb hB
  have hc : (0 : ℝ) < Real.exp b := Real.exp_pos b
  have hintE : Integrable (fun u : ℝ => Real.exp u * φ u) :=
    (Real.continuous_exp.mul hφ).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hasCompactSupport_of_tails hb hB))
  -- Mathlib's substitution, with log (exp x) = x collapsing the inner composite
  have hsub : ∫ x in Ioi b, Real.exp x * φ x
      = ∫ y in Ioi (Real.exp b), φ (Real.log y) := by
    have := integral_comp_exp_Ioi (fun y : ℝ => φ (Real.log y)) b
    simpa [smul_eq_mul, Real.log_exp] using this
  have hIO : IntegrableOn (fun x : ℝ => φ (Real.log x)) (Ioi (Real.exp b)) := by
    have := (integrableOn_comp_exp_Ioi (fun y : ℝ => φ (Real.log y)) b).1
      (by simpa [smul_eq_mul, Real.log_exp] using hintE.integrableOn)
    exact this
  have hstep1 : ∫ x in Ioi (0 : ℝ), φ (Real.log x)
      = ∫ x in Ioi (Real.exp b), φ (Real.log x) :=
    integral_Ioi_zero_eq_Ioi hc (comp_log_vanishes hb) hIO
  have hstep3 : ∫ x in Ioi b, Real.exp x * φ x = ∫ u : ℝ, Real.exp u * φ u :=
    integral_Ioi_eq_integral (fun x hx => by rw [hb x hx, mul_zero]) hintE
  rw [hstep1, ← hsub, hstep3]
  simp_rw [mul_comm]

end Transport

/-! ### The multiplicative packet -/

/-- The guard is not cosmetic: `Real.log` is even and `log 0 = 0`, so without it
any value the composite takes is mirrored onto the negative axis, and `0` is hit
as well — neither is compatible with `tsupport ⊆ Ioi 0`. -/
def mulPacket (φ : ℝ → ℝ) : ℝ → ℝ := fun x => if 0 < x then φ (Real.log x) else 0

section Packet

variable {φ : ℝ → ℝ} {b B : ℝ}

theorem mulPacket_of_pos {x : ℝ} (hx : 0 < x) : mulPacket φ x = φ (Real.log x) :=
  if_pos hx

theorem mulPacket_of_nonpos {x : ℝ} (hx : x ≤ 0) : mulPacket φ x = 0 :=
  if_neg (not_lt.2 hx)

/-- Below `exp b` the packet is identically zero — both because of the guard and
because `φ` vanishes there. -/
theorem mulPacket_eq_zero_below (hb : ∀ u ≤ b, φ u = 0) {x : ℝ}
    (hx : x ≤ Real.exp b) : mulPacket φ x = 0 := by
  rcases le_or_gt x 0 with h | h
  · exact mulPacket_of_nonpos h
  · rw [mulPacket_of_pos h]
    refine hb _ ?_
    have := (Real.log_le_log_iff h (Real.exp_pos b)).2 hx
    rwa [Real.log_exp] at this

theorem mulPacket_eq_zero_above (hB : ∀ u, B ≤ u → φ u = 0) {x : ℝ}
    (hx : Real.exp B ≤ x) : mulPacket φ x = 0 := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos B) hx
  rw [mulPacket_of_pos hxpos]
  refine hB _ ?_
  have := (Real.log_le_log_iff (Real.exp_pos B) hxpos).2 hx
  rwa [Real.log_exp] at this

/-- `tsupport` lands inside a compact subinterval of `Ioi 0`. -/
theorem tsupport_mulPacket_subset (hb : ∀ u ≤ b, φ u = 0) (hB : ∀ u, B ≤ u → φ u = 0) :
    tsupport (mulPacket φ) ⊆ Icc (Real.exp b) (Real.exp B) := by
  refine closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hnot
  refine hx ?_
  rcases not_and_or.mp (fun h => hnot ⟨h.1, h.2⟩) with h | h
  · exact mulPacket_eq_zero_below hb (le_of_not_ge h)
  · exact mulPacket_eq_zero_above hB (le_of_not_ge h)

theorem mulPacket_hasCompactSupport (hb : ∀ u ≤ b, φ u = 0) (hB : ∀ u, B ≤ u → φ u = 0) :
    HasCompactSupport (mulPacket φ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := Real.exp b) (b := Real.exp B)) ?_
  intro x hx
  rcases not_and_or.mp (fun h => hx ⟨h.1, h.2⟩) with h | h
  · exact mulPacket_eq_zero_below hb (le_of_not_ge h)
  · exact mulPacket_eq_zero_above hB (le_of_not_ge h)

/-- Smoothness.  `Ioi 0` and `Iio (exp b)` are open and cover ℝ; on the first the
packet is `φ ∘ log`, on the second it is `0`. -/
theorem mulPacket_contDiff (hφ : ContDiff ℝ ∞ φ) (hb : ∀ u ≤ b, φ u = 0) :
    ContDiff ℝ ∞ (mulPacket φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · have hEq : mulPacket φ =ᶠ[𝓝 x] fun y => φ (Real.log y) :=
      eventuallyEq_of_mem (Ioi_mem_nhds hx) (fun y hy => mulPacket_of_pos hy)
    exact ContDiffAt.congr_of_eventuallyEq
      (hφ.contDiffAt.comp x (Real.contDiffAt_log.2 (ne_of_gt hx))) hEq
  · have hmem : Iio (Real.exp b) ∈ 𝓝 x :=
      Iio_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos b))
    have hEq : mulPacket φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      eventuallyEq_of_mem hmem (fun y hy => mulPacket_eq_zero_below hb (le_of_lt hy))
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hEq

/-- On `Ioi 0` the packet IS the composite, so the transported moments apply. -/
theorem integral_mulPacket_inv (hφ : Continuous φ)
    (hb : ∀ u ≤ b, φ u = 0) (hB : ∀ u, B ≤ u → φ u = 0) :
    ∫ x in Ioi (0 : ℝ), x⁻¹ * mulPacket φ x = ∫ u : ℝ, φ u := by
  rw [← integral_inv_mul_comp_log hφ hb hB]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [mulPacket_of_pos hx]

theorem integral_mulPacket (hφ : Continuous φ)
    (hb : ∀ u ≤ b, φ u = 0) (hB : ∀ u, B ≤ u → φ u = 0) :
    ∫ x in Ioi (0 : ℝ), mulPacket φ x = ∫ u : ℝ, φ u * Real.exp u := by
  rw [← integral_comp_log hφ hb hB]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [mulPacket_of_pos hx]

end Packet

end AEGIS.WeilLogTransportCanonicalV1
