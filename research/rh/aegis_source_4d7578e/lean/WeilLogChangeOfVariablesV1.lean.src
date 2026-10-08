/-
AEGIS Ω — the log change of variables x = e^u, V1.  (Step (ii).)

`WeilArchimedeanPacketWitnessV1` listed three things needed to discharge
`ArchimedeanPacketReductionV1`:

  (i)   a packet whose log-support sits inside [-1/32, 1/32]   — PROVED there;
  (ii)  the change of variables x = e^u                        — THIS MODULE;
  (iii) autocorrelation vanishing outside the log-support      — still OPEN.

`WeilMomentKillerConstructionV1` proved that φ = ψ' + ψ'' kills both additive
moments, ∫_ℝ φ = 0 and ∫_ℝ φ(u) e^u du = 0, but explicitly did NOT claim
`WeilMomentConditionsV1`, which is a statement about multiplicative integrals
∫_{Ioi 0} g dx/x and ∫_{Ioi 0} g dx for g : ℝ → ℂ.  This module supplies the
missing transport and then discharges that statement.

THE TRANSPORT

Mathlib has `integral_comp_log_Ioi` and `integral_comp_exp_Ioi`, but only over
`Ioi a` with `a > 0` — neither reaches down to 0, because in the log coordinate
that is -∞.  Compact support is exactly what bridges the gap: if φ vanishes on
`Iic b` then the multiplicative integrand vanishes on `Ioc 0 (exp b)`, so the
integral over `Ioi 0` already equals the integral over `Ioi (exp b)`, where
Mathlib's lemma applies.  `integral_Ioi_zero_eq_Ioi` and
`integral_Ioi_eq_integral` are those two extensions, and they are the only
analytic content here; the rest is bookkeeping.

    ∫_{Ioi 0} x⁻¹ φ(log x) dx = ∫_ℝ φ(u) du
    ∫_{Ioi 0} φ(log x) dx     = ∫_ℝ φ(u) e^u du

THE PACKET IS A MEMBER, NOT JUST AN INTEGRAND

`mulPacket φ x = if 0 < x then φ (log x) else 0` needs the guard: Mathlib's
`Real.log` is even (`log (-x) = log x`) and `log 0 = 0`, so the unguarded
composite `φ ∘ log` takes the same value at `-x` as at `x`.  Any value it takes
inside the support is therefore mirrored onto the negative axis, which
`tsupport ⊆ Ioi 0` forbids.  (This module proves the evenness, which is the
mechanism; it does not compute `phi0 0` and so does not claim the unguarded
composite is in fact nonzero at any particular mirrored point.)

Smoothness of the guarded function is proved, not assumed: `Ioi 0` and
`Iio (exp b)` are two open sets covering ℝ (because `exp b > 0`), the packet is
`φ ∘ log` on the first and identically `0` on the second, so `ContDiffAt` holds
at every point by `ContDiffAt.congr_of_eventuallyEq`.

WHAT THIS CLOSES

`weilMomentConditions_gWitness` discharges `WeilMomentConditionsV1` for the
concrete ℂ-valued packet `gWitness` built from `phi0`, and the restated
definitions it is stated against were diffed byte-identical against
`WeilCriterionCompactSmoothV1.lean` on `proof/weil-analytic-v21-probe`.

`gWitness_log_support` then shows the SAME packet also satisfies (i): its
support sits inside [exp(-1/32), exp(1/32)].  So steps (i) and (ii) are
discharged by one object, not by two different ones — the bump packet of
`WeilArchimedeanPacketWitnessV1` satisfied (i) but provably could not satisfy
the moment conditions, and is superseded here.

WHAT THIS DOES NOT CLOSE

Step (iii), autocorrelation vanishing outside the log-support, is untouched.
`ArchimedeanPacketReductionV1` is still quantified over and never constructed —
its `reduction` field asserts `arch = D * nrm2`, an identity about the
archimedean form, and nothing here computes that form.

`ANALYTIC_DIAGONAL_LOWER_V1`, the global Weil sign and RH all remain OPEN.
This module proves no sign and no part of RH.
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic
import WeilMomentKillerConstructionV1

open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace AEGIS.WeilLogChangeOfVariablesV1

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

/-! ### Instantiation at `phi0`, and `WeilMomentConditionsV1` -/

/-- The compact-smooth domain, restated verbatim from
`WeilCriterionCompactSmoothV1.lean` on `proof/weil-analytic-v21-probe`. -/
def WeilCompactSmoothGV1 :=
  { g : ℝ → ℂ // ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Set.Ioi 0 }

/-- Restated verbatim from the same source. -/
def WeilMomentConditionsV1 (g : WeilCompactSmoothGV1) : Prop :=
  (∫ x in Set.Ioi (0 : ℝ), g.1 x / (x : ℂ)) = 0 ∧
  (∫ x in Set.Ioi (0 : ℝ), g.1 x) = 0

/-- The support is actually inside the bump radius `1/40`, strictly smaller than
the `1/32` window.  That strictness is what the tail hypotheses need. -/
theorem phi0_tsupport_Icc : tsupport phi0 ⊆ Icc (-(1 / 40) : ℝ) (1 / 40) := by
  refine (tsupport_momentKiller_subset psi0).trans ?_
  rw [psi0_tsupport, Real.closedBall_eq_Icc]
  exact Icc_subset_Icc (by norm_num) (by norm_num)

theorem phi0_vanishes_below : ∀ u ≤ -(1 / 32 : ℝ), phi0 u = 0 := by
  intro u hu
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  have := phi0_tsupport_Icc hmem
  linarith [this.1]

theorem phi0_vanishes_above : ∀ u, (1 / 32 : ℝ) ≤ u → phi0 u = 0 := by
  intro u hu
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  have := phi0_tsupport_Icc hmem
  linarith [this.2]

theorem phi0_continuous : Continuous phi0 :=
  (momentKiller_contDiff psi0_contDiff).continuous

/-- The ℂ-valued multiplicative packet. -/
def gPacket : ℝ → ℂ := fun x => ((mulPacket phi0 x : ℝ) : ℂ)

theorem gPacket_contDiff : ContDiff ℝ ∞ gPacket :=
  Complex.ofRealCLM.contDiff.comp
    (mulPacket_contDiff (momentKiller_contDiff psi0_contDiff) phi0_vanishes_below)

theorem gPacket_support : Function.support gPacket = Function.support (mulPacket phi0) := by
  ext x
  simp [gPacket, Function.mem_support, Complex.ofReal_eq_zero]

theorem gPacket_hasCompactSupport : HasCompactSupport gPacket := by
  rw [HasCompactSupport, tsupport, gPacket_support, ← tsupport]
  exact mulPacket_hasCompactSupport phi0_vanishes_below phi0_vanishes_above

theorem gPacket_tsupport_subset : tsupport gPacket ⊆ Set.Ioi 0 := by
  rw [tsupport, gPacket_support, ← tsupport]
  refine (tsupport_mulPacket_subset phi0_vanishes_below phi0_vanishes_above).trans ?_
  intro x hx
  exact lt_of_lt_of_le (Real.exp_pos _) hx.1

/-- The concrete member of the domain. -/
def gWitness : WeilCompactSmoothGV1 :=
  ⟨gPacket, gPacket_contDiff, gPacket_hasCompactSupport, gPacket_tsupport_subset⟩

/-- **Step (ii) discharged.**  The moment-killed packet, transported to the
multiplicative line, satisfies both conditions of `WeilMomentConditionsV1`. -/
theorem weilMomentConditions_gWitness : WeilMomentConditionsV1 gWitness := by
  constructor
  · have hreal : ∫ x in Ioi (0 : ℝ), x⁻¹ * mulPacket phi0 x = 0 := by
      rw [integral_mulPacket_inv phi0_continuous phi0_vanishes_below phi0_vanishes_above]
      exact phi0_moments.1
    have : ∫ x in Ioi (0 : ℝ), gWitness.1 x / (x : ℂ)
        = ((∫ x in Ioi (0 : ℝ), x⁻¹ * mulPacket phi0 x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      show ((mulPacket phi0 x : ℝ) : ℂ) / (x : ℂ) = _
      rw [Complex.ofReal_mul, Complex.ofReal_inv]
      field_simp
    rw [this, hreal, Complex.ofReal_zero]
  · have hreal : ∫ x in Ioi (0 : ℝ), mulPacket phi0 x = 0 := by
      rw [integral_mulPacket phi0_continuous phi0_vanishes_below phi0_vanishes_above]
      exact phi0_moments.2
    have : ∫ x in Ioi (0 : ℝ), gWitness.1 x
        = ((∫ x in Ioi (0 : ℝ), mulPacket phi0 x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      rfl
    rw [this, hreal, Complex.ofReal_zero]

/-- CONTROL (non-vacuity): the witness is not the zero function, so the two
vanishing moments are not satisfied trivially. -/
theorem gWitness_ne_zero : gWitness.1 ≠ 0 := by
  intro h
  refine phi0_ne_zero (funext fun u => ?_)
  simp only [Pi.zero_apply]
  have hx : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hc := congrFun h (Real.exp u)
  simp only [Pi.zero_apply] at hc
  have hc2 : ((mulPacket phi0 (Real.exp u) : ℝ) : ℂ) = 0 := hc
  rw [mulPacket_of_pos hx, Real.log_exp] at hc2
  exact_mod_cast hc2

/-- CONTROL (the guard is load-bearing): `Real.log` is even, so the unguarded
composite takes the same value at `-x` as at `x`.  That symmetry is exactly what
`tsupport ⊆ Ioi 0` forbids, and it is why `mulPacket` carries the `if 0 < x`.
This records the mechanism; it does not evaluate `phi0` anywhere. -/
theorem log_is_even_so_guard_needed (x : ℝ) : Real.log (-x) = Real.log x :=
  Real.log_neg_eq_log x

/-- **The same packet also satisfies step (i).**  Its support sits inside the
certificate's width-1/32 window, in exactly the form
`WeilArchimedeanPacketWitnessV1.packet_log_support` had it. -/
theorem gWitness_log_support :
    tsupport gWitness.1 ⊆ Icc (Real.exp (-(1 / 32))) (Real.exp (1 / 32)) := by
  show tsupport gPacket ⊆ _
  rw [tsupport, gPacket_support, ← tsupport]
  exact tsupport_mulPacket_subset phi0_vanishes_below phi0_vanishes_above

end AEGIS.WeilLogChangeOfVariablesV1

#print axioms AEGIS.WeilLogChangeOfVariablesV1.integral_Ioi_zero_eq_Ioi
#print axioms AEGIS.WeilLogChangeOfVariablesV1.integral_Ioi_eq_integral
#print axioms AEGIS.WeilLogChangeOfVariablesV1.integral_inv_mul_comp_log
#print axioms AEGIS.WeilLogChangeOfVariablesV1.integral_comp_log
#print axioms AEGIS.WeilLogChangeOfVariablesV1.mulPacket_contDiff
#print axioms AEGIS.WeilLogChangeOfVariablesV1.tsupport_mulPacket_subset
#print axioms AEGIS.WeilLogChangeOfVariablesV1.gPacket_tsupport_subset
#print axioms AEGIS.WeilLogChangeOfVariablesV1.weilMomentConditions_gWitness
#print axioms AEGIS.WeilLogChangeOfVariablesV1.gWitness_ne_zero
#print axioms AEGIS.WeilLogChangeOfVariablesV1.gWitness_log_support
