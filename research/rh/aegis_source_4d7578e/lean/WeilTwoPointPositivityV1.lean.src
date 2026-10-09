import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
Four phase tests bound a two-point Hermitian quadratic expression. This is
the finite algebra step in the restricted Weil criterion's translated-kernel
argument. It does not assert that the actual zeta form passes these tests.
The translation identity and Laplace/residue argument remain separate.
-/

open Complex

set_option autoImplicit false

noncomputable section

/-- Four phases suffice for a uniform bound; arbitrary phases are unnecessary. -/
def WeilFourPhaseV1 (c : ℂ) : Prop :=
  c = 1 ∨ c = -1 ∨ c = I ∨ c = -I

/-- Value of the two-point Hermitian form with equal real diagonal `a`. -/
def WeilTwoPointValueV1 (a : ℝ) (z c : ℂ) : ℝ :=
  a * (1 + normSq c) + 2 * (c * z).re

/-- Passing the four phase tests controls both components of the cross term. -/
theorem weil_four_phase_nonnegative_components_v1 (a : ℝ) (z : ℂ)
    (h : ∀ c : ℂ, WeilFourPhaseV1 c → 0 ≤ WeilTwoPointValueV1 a z c) :
    |z.re| ≤ a ∧ |z.im| ≤ a := by
  have hp := h 1 (Or.inl rfl)
  have hn := h (-1) (Or.inr (Or.inl rfl))
  have hi := h I (Or.inr (Or.inr (Or.inl rfl)))
  have hni := h (-I) (Or.inr (Or.inr (Or.inr rfl)))
  simp [WeilTwoPointValueV1, Complex.normSq_apply, Complex.mul_re] at hp hn hi hni
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A uniform bound sufficient for the subsequent Laplace-transform argument.
The constant 2 is deliberately sufficient; it is not the sharp PSD bound. -/
theorem weil_four_phase_nonnegative_norm_bound_v1 (a : ℝ) (z : ℂ)
    (h : ∀ c : ℂ, WeilFourPhaseV1 c → 0 ≤ WeilTwoPointValueV1 a z c) :
    ‖z‖ ≤ 2 * a := by
  obtain ⟨hr, hi⟩ := weil_four_phase_nonnegative_components_v1 a z h
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 2 * a := by linarith

/-- If the cross term exceeds that bound, one of the four actual phase tests
is negative. This is an existence theorem, not a claim that zeta has such a term. -/
theorem weil_four_phase_negative_witness_v1 (a : ℝ) (z : ℂ)
    (hlarge : 2 * a < ‖z‖) :
    ∃ c : ℂ, WeilFourPhaseV1 c ∧ WeilTwoPointValueV1 a z c < 0 := by
  classical
  by_contra h
  push_neg at h
  have hbound := weil_four_phase_nonnegative_norm_bound_v1 a z h
  linarith

#print axioms weil_four_phase_nonnegative_components_v1
#print axioms weil_four_phase_nonnegative_norm_bound_v1
#print axioms weil_four_phase_negative_witness_v1
