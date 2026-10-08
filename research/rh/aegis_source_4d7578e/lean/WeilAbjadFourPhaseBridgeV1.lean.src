import WeilTwoPointPositivityV1
import Mathlib.Tactic

/-!
# Abjad triadic routing as the existing four-phase Weil carrier

This file formalizes only an arithmetic/phase encoding bridge.

The AEGIS Abjad runtime routes an integer sum to a dodecagonal node modulo 12,
and calls digital-root values 3, 6, and 9 triadic. Arithmetically this is the
same as divisibility by 3. Hence a triadic sum lands at exactly one of the
four dodecagon nodes 0, 3, 6, or 9. Mapping those quarter-turn nodes to
`1, I, -1, -I` gives exactly `WeilFourPhaseV1` from
`WeilTwoPointPositivityV1`.

This is a carrier equivalence. It does not establish nonnegativity for the
zeta/Weil form, global Weil positivity, or the Riemann Hypothesis.
-/

open Complex

set_option autoImplicit false

noncomputable section

/-- Dodecagonal routing node of an integer Abjad sum. -/
def AbjadNodeV1 (s : ℕ) : ℕ := s % 12

/-- Arithmetic content of the runtime's triadic digital-root classification. -/
def AbjadTriadicSumV1 (s : ℕ) : Prop := s % 3 = 0

/-- The four quarter-turn nodes on the 12-node Abjad routing ring. -/
def AbjadTriadicNodeV1 (r : ℕ) : Prop :=
  r = 0 ∨ r = 3 ∨ r = 6 ∨ r = 9

/-- A sum is triadic exactly when its dodecagonal residue is 0, 3, 6, or 9. -/
theorem abjad_triadic_sum_iff_node_v1 (s : ℕ) :
    AbjadTriadicSumV1 s ↔ AbjadTriadicNodeV1 (AbjadNodeV1 s) := by
  simp only [AbjadTriadicSumV1, AbjadTriadicNodeV1, AbjadNodeV1]
  omega

/-- Quarter-turn phase attached to a dodecagonal node.
Only the values at triadic nodes carry theorem authority. -/
def AbjadPhaseV1 (r : ℕ) : ℂ :=
  if r = 0 then 1
  else if r = 3 then I
  else if r = 6 then -1
  else -I

/-- Phase attached directly to an integer Abjad sum. -/
def AbjadSumPhaseV1 (s : ℕ) : ℂ := AbjadPhaseV1 (AbjadNodeV1 s)

/-- Every triadic Abjad node maps to one of the four phases already used by
`WeilFourPhaseV1`. -/
theorem abjad_phase_four_phase_v1 (r : ℕ)
    (hr : AbjadTriadicNodeV1 r) :
    WeilFourPhaseV1 (AbjadPhaseV1 r) := by
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [AbjadPhaseV1, WeilFourPhaseV1]

/-- Conversely every existing Weil four-phase value has a triadic Abjad node. -/
theorem four_phase_has_abjad_node_v1 (c : ℂ)
    (hc : WeilFourPhaseV1 c) :
    ∃ r : ℕ, AbjadTriadicNodeV1 r ∧ AbjadPhaseV1 r = c := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨0, Or.inl rfl, by simp [AbjadPhaseV1]⟩
  · exact ⟨6, Or.inr (Or.inr (Or.inl rfl)), by simp [AbjadPhaseV1]⟩
  · exact ⟨3, Or.inr (Or.inl rfl), by simp [AbjadPhaseV1]⟩
  · exact ⟨9, Or.inr (Or.inr (Or.inr rfl)), by simp [AbjadPhaseV1]⟩

/-- Quantifying over triadic Abjad nodes is exactly equivalent to quantifying
over the existing four-phase Weil carrier. -/
theorem abjad_phase_forall_iff_four_phase_v1 (P : ℂ → Prop) :
    (∀ r : ℕ, AbjadTriadicNodeV1 r → P (AbjadPhaseV1 r)) ↔
      (∀ c : ℂ, WeilFourPhaseV1 c → P c) := by
  constructor
  · intro h c hc
    obtain ⟨r, hr, hphase⟩ := four_phase_has_abjad_node_v1 c hc
    rw [← hphase]
    exact h r hr
  · intro h r hr
    exact h (AbjadPhaseV1 r) (abjad_phase_four_phase_v1 r hr)

/-- Classical one-letter Abjad values furnishing the four quarter-turn phases:
60 (sin) -> 0 -> 1, 3 (jim) -> 3 -> I,
6 (waw) -> 6 -> -1, and 9 (ta) -> 9 -> -I. -/
theorem abjad_classical_witness_phases_v1 :
    AbjadSumPhaseV1 60 = 1 ∧
    AbjadSumPhaseV1 3 = I ∧
    AbjadSumPhaseV1 6 = -1 ∧
    AbjadSumPhaseV1 9 = -I := by
  norm_num [AbjadSumPhaseV1, AbjadNodeV1, AbjadPhaseV1]

/-- Existing four-phase nonnegativity transfers without loss to the Abjad
triadic-node carrier. This bounds the two real components of the cross term;
it does not assert that the zeta form satisfies the hypotheses. -/
theorem weil_abjad_triadic_nonnegative_components_v1 (a : ℝ) (z : ℂ)
    (h : ∀ r : ℕ, AbjadTriadicNodeV1 r →
      0 ≤ WeilTwoPointValueV1 a z (AbjadPhaseV1 r)) :
    |z.re| ≤ a ∧ |z.im| ≤ a := by
  apply weil_four_phase_nonnegative_components_v1 a z
  intro c hc
  obtain ⟨r, hr, hphase⟩ := four_phase_has_abjad_node_v1 c hc
  rw [← hphase]
  exact h r hr

/-- If the existing two-point norm obstruction is large enough, a negative
witness can be represented by a triadic Abjad node. This is only a witness
carrier theorem, not an unconditional negative zeta witness. -/
theorem weil_abjad_triadic_negative_witness_v1 (a : ℝ) (z : ℂ)
    (hlarge : 2 * a < ‖z‖) :
    ∃ r : ℕ, AbjadTriadicNodeV1 r ∧
      WeilTwoPointValueV1 a z (AbjadPhaseV1 r) < 0 := by
  obtain ⟨c, hc, hneg⟩ := weil_four_phase_negative_witness_v1 a z hlarge
  obtain ⟨r, hr, hphase⟩ := four_phase_has_abjad_node_v1 c hc
  refine ⟨r, hr, ?_⟩
  rw [hphase]
  exact hneg

/-- The four phase tests are not merely sufficient: they are exactly the box
condition on the real and imaginary parts of the cross term. -/
theorem weil_four_phase_nonnegative_iff_components_v1 (a : ℝ) (z : ℂ) :
    (∀ c : ℂ, WeilFourPhaseV1 c → 0 ≤ WeilTwoPointValueV1 a z c) ↔
      (|z.re| ≤ a ∧ |z.im| ≤ a) := by
  constructor
  · exact weil_four_phase_nonnegative_components_v1 a z
  · rintro ⟨hr, hi⟩ c hc
    rcases abs_le.mp hr with ⟨hrlo, hrhi⟩
    rcases abs_le.mp hi with ⟨hilo, hihi⟩
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [WeilTwoPointValueV1, Complex.normSq_apply, Complex.mul_re] <;>
      linarith

/-- Therefore Abjad-triadic nonnegativity is exactly the same component-box
condition. This isolates the precise scalar inequality that any later global
zeta/Weil positivity proof must establish. -/
theorem weil_abjad_triadic_nonnegative_iff_components_v1 (a : ℝ) (z : ℂ) :
    (∀ r : ℕ, AbjadTriadicNodeV1 r →
      0 ≤ WeilTwoPointValueV1 a z (AbjadPhaseV1 r)) ↔
      (|z.re| ≤ a ∧ |z.im| ≤ a) := by
  constructor
  · exact weil_abjad_triadic_nonnegative_components_v1 a z
  · intro h r hr
    have hall := (weil_four_phase_nonnegative_iff_components_v1 a z).2 h
    exact hall (AbjadPhaseV1 r) (abjad_phase_four_phase_v1 r hr)

/-- Discrete Fourier reconstruction on the four triadic dodecagon nodes.
The opposite-node sums recover the diagonal term, while their differences
recover the two real coordinates of the cross term. -/
theorem weil_abjad_phase_reconstruction_v1 (a : ℝ) (z : ℂ) :
    WeilTwoPointValueV1 a z (AbjadPhaseV1 0) +
        WeilTwoPointValueV1 a z (AbjadPhaseV1 6) = 4 * a ∧
    WeilTwoPointValueV1 a z (AbjadPhaseV1 3) +
        WeilTwoPointValueV1 a z (AbjadPhaseV1 9) = 4 * a ∧
    WeilTwoPointValueV1 a z (AbjadPhaseV1 0) -
        WeilTwoPointValueV1 a z (AbjadPhaseV1 6) = 4 * z.re ∧
    WeilTwoPointValueV1 a z (AbjadPhaseV1 9) -
        WeilTwoPointValueV1 a z (AbjadPhaseV1 3) = 4 * z.im := by
  constructor
  · simp [AbjadPhaseV1, WeilTwoPointValueV1, Complex.normSq_apply, Complex.mul_re]
    ring
  · constructor
    · simp [AbjadPhaseV1, WeilTwoPointValueV1, Complex.normSq_apply, Complex.mul_re]
      ring
    · constructor
      · simp [AbjadPhaseV1, WeilTwoPointValueV1, Complex.normSq_apply, Complex.mul_re]
        ring
      · simp [AbjadPhaseV1, WeilTwoPointValueV1, Complex.normSq_apply, Complex.mul_re]
        ring

#print axioms abjad_triadic_sum_iff_node_v1
#print axioms abjad_phase_four_phase_v1
#print axioms four_phase_has_abjad_node_v1
#print axioms abjad_phase_forall_iff_four_phase_v1
#print axioms abjad_classical_witness_phases_v1
#print axioms weil_abjad_triadic_nonnegative_components_v1
#print axioms weil_abjad_triadic_negative_witness_v1
#print axioms weil_four_phase_nonnegative_iff_components_v1
#print axioms weil_abjad_triadic_nonnegative_iff_components_v1
#print axioms weil_abjad_phase_reconstruction_v1
