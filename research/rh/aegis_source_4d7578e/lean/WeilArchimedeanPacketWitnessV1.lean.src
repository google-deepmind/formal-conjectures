/-
AEGIS Ω — a concrete width-1/32 packet witness, V1.

`WeilDiagonalConstantFromCothTailV1` leaves `ArchimedeanPacketReductionV1`
quantified over and never constructed.  Discharging it needs three things:

  (i)   a concrete `WeilCompactSmoothGV1` witness whose log-support sits inside
        the certificate window [-1/32, 1/32];
  (ii)  the change of variables x = e^u turning (x - x⁻¹) into 2 sinh u;
  (iii) vanishing of the autocorrelation outside that log-support.

This module supplies (i), and only (i).

`packet` is a `ContDiffBump` centred at the multiplicative identity with outer
radius 1/40, pushed into ℂ.  `packet_log_support` is the point of the file:

    tsupport packet.1 ⊆ Icc (exp (-(1/32))) (exp (1/32))

so the packet lives strictly inside the window the coth tail was computed for.
The radius 1/40 is not arbitrary — 41/40 ≤ 33/32 ≤ exp(1/32) and
exp(-(1/32)) ≤ 32/33 ≤ 39/40, both from `Real.add_one_le_exp` alone, with
integer margins 1320 - 1312 = 8 and 1287 - 1280 = 7.  A radius of 1/32 would
fail the lower bound.

WHAT THIS IS NOT

`packet` does **not** satisfy `WeilMomentConditionsV1`.  It cannot: the bump is
nonnegative and not identically zero, so `∫_{Ioi 0} packet > 0 ≠ 0`.  The
certificate needs a packet with BOTH moments vanishing, and that is a separate
construction, not a missing lemma about this one.

The route for it is identified and recorded here so the next module has a
target rather than a search.  In the log coordinate u = log x, writing
g(x) = φ(log x),

    ∫_{Ioi 0} g(x) dx/x = ∫_ℝ φ(u) du        and
    ∫_{Ioi 0} g(x) dx   = ∫_ℝ φ(u) e^u du.

Take φ = ψ' + ψ'' for ANY smooth compactly supported ψ.  Then ∫φ = 0 because φ
is a derivative of a compactly supported function, and

    ∫ φ e^u = ∫ ψ' e^u + ∫ ψ'' e^u = -∫ ψ e^u + ∫ ψ e^u = 0

by parts twice, boundary terms vanishing.  Both moments die for every ψ, and
supp φ ⊆ supp ψ, so the window is preserved.  Non-triviality also follows: if
ψ' + ψ'' ≡ 0 then ψ' = C e^{-u} and ψ = -C e^{-u} + D, which is compactly
supported only for C = D = 0.

None of that paragraph is proved here.  It is a plan, not a theorem.

`ANALYTIC_DIAGONAL_LOWER_V1`, the global Weil sign and RH all remain OPEN.
This module proves no sign and no part of RH.
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Set Metric
open scoped ContDiff

noncomputable section

namespace AEGIS.WeilArchimedeanPacketWitnessV1

/-- The compact-smooth domain, restated verbatim from
`WeilCriterionCompactSmoothV1.lean` on `proof/weil-analytic-v21-probe`. -/
def WeilCompactSmoothGV1 :=
  { g : ℝ → ℂ // ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Set.Ioi 0 }

/-- The bump, centred at the multiplicative identity. -/
def bump : ContDiffBump (1 : ℝ) where
  rIn := 1 / 80
  rOut := 1 / 40
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The packet as a ℂ-valued function. -/
def packetFun : ℝ → ℂ := fun x => ((bump x : ℝ) : ℂ)

/-! ### Support -/

theorem packetFun_support : Function.support packetFun = Function.support (bump : ℝ → ℝ) := by
  ext x
  simp [packetFun, Function.mem_support, Complex.ofReal_eq_zero]

theorem packetFun_tsupport : tsupport packetFun = closedBall (1 : ℝ) (1 / 40) := by
  rw [tsupport, packetFun_support, ← tsupport, bump.tsupport_eq]
  norm_num [bump]

theorem packetFun_tsupport_eq_Icc :
    tsupport packetFun = Icc (39 / 40 : ℝ) (41 / 40) := by
  rw [packetFun_tsupport, Real.closedBall_eq_Icc]
  norm_num

theorem packetFun_hasCompactSupport : HasCompactSupport packetFun := by
  rw [HasCompactSupport, packetFun_tsupport]
  exact isCompact_closedBall _ _

theorem packetFun_contDiff : ContDiff ℝ ∞ packetFun :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

theorem packetFun_tsupport_subset_Ioi : tsupport packetFun ⊆ Set.Ioi 0 := by
  rw [packetFun_tsupport_eq_Icc]
  intro x hx
  exact lt_of_lt_of_le (by norm_num) hx.1

/-- The concrete witness. -/
def packet : WeilCompactSmoothGV1 :=
  ⟨packetFun, packetFun_contDiff, packetFun_hasCompactSupport,
    packetFun_tsupport_subset_Ioi⟩

/-! ### The window bounds -/

theorem exp_one_div_32_ge : (33 : ℝ) / 32 ≤ Real.exp (1 / 32) := by
  have h := Real.add_one_le_exp ((1 : ℝ) / 32)
  linarith

theorem exp_neg_one_div_32_le : Real.exp (-(1 / 32)) ≤ (32 : ℝ) / 33 := by
  have hpos : (0 : ℝ) < Real.exp (1 / 32) := Real.exp_pos _
  rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]
  have := exp_one_div_32_ge
  linarith

theorem upper_bound : (41 : ℝ) / 40 ≤ Real.exp (1 / 32) :=
  le_trans (by norm_num) exp_one_div_32_ge

theorem lower_bound : Real.exp (-(1 / 32)) ≤ (39 : ℝ) / 40 :=
  le_trans exp_neg_one_div_32_le (by norm_num)

/-! ### The point of the file -/

/-- **The log-support control.**  The packet lives strictly inside the
certificate's width-1/32 window. -/
theorem packet_log_support :
    tsupport packet.1 ⊆ Icc (Real.exp (-(1 / 32))) (Real.exp (1 / 32)) := by
  show tsupport packetFun ⊆ _
  rw [packetFun_tsupport_eq_Icc]
  exact Icc_subset_Icc lower_bound upper_bound

/-! ### Controls -/

/-- CONTROL (non-vacuity): the packet is not the zero function.  A witness that
was identically zero would satisfy every support constraint and mean nothing. -/
theorem packet_ne_zero : packet.1 1 = 1 := by
  show packetFun 1 = 1
  have h : bump (1 : ℝ) = 1 :=
    bump.one_of_mem_closedBall (by simp [Metric.mem_closedBall, bump])
  simp [packetFun, h]

/-- CONTROL: the window containment is strict at both ends, so the radius has
room and is not sitting exactly on the boundary. -/
theorem packet_window_strict :
    Real.exp (-(1 / 32)) < 39 / 40 ∧ (41 : ℝ) / 40 < Real.exp (1 / 32) :=
  ⟨lt_of_le_of_lt exp_neg_one_div_32_le (by norm_num),
    lt_of_lt_of_le (by norm_num) exp_one_div_32_ge⟩

/-- CONTROL (the honest negative): the witness does NOT have vanishing first
moment, so it does not satisfy `WeilMomentConditionsV1`.  Recorded as the
pointwise fact that drives it — the bump is nonneg and positive at 1. -/
theorem packet_nonneg_and_positive_at_one :
    (∀ x : ℝ, 0 ≤ (bump x : ℝ)) ∧ (0 : ℝ) < bump 1 :=
  ⟨fun x => bump.nonneg, by
    have h : bump (1 : ℝ) = 1 :=
      bump.one_of_mem_closedBall (by simp [Metric.mem_closedBall, bump])
    rw [h]; norm_num⟩

end AEGIS.WeilArchimedeanPacketWitnessV1

#print axioms AEGIS.WeilArchimedeanPacketWitnessV1.packetFun_tsupport_eq_Icc
#print axioms AEGIS.WeilArchimedeanPacketWitnessV1.packetFun_contDiff
#print axioms AEGIS.WeilArchimedeanPacketWitnessV1.packetFun_hasCompactSupport
#print axioms AEGIS.WeilArchimedeanPacketWitnessV1.packet_log_support
#print axioms AEGIS.WeilArchimedeanPacketWitnessV1.packet_ne_zero
#print axioms AEGIS.WeilArchimedeanPacketWitnessV1.packet_window_strict
#print axioms AEGIS.WeilArchimedeanPacketWitnessV1.packet_nonneg_and_positive_at_one
