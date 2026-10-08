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

import WeilSeparatedArchBridgeV31
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
AEGIS Ω — compact log-window exhaustion bridge V1.

This module closes one purely logical globalization boundary.

Every repository Weil packet has compact support on the positive half-line.
After the logarithmic lift
  h(t) = exp(t/2) * g(exp t),
that support is contained in some finite symmetric interval [-L,L].

Therefore universal arithmetic nonpositivity on the existing compact-smooth,
two-moment test class is equivalent to proving the same inequality on every
finite log window L>0.

This theorem does NOT prove any finite-window sign estimate, uniform control as
L grows, global Weil positivity, the Weil criterion-to-RH implication, or RH.
It only proves that "all finite windows" is exactly the full compact-support
sign obligation; no density or limiting approximation is needed for this
specific exhaustion step.

ARBITRARY_WINDOW_NONPOSITIVITY_OPEN
GLOBAL_WEIL_POSITIVITY_NOT_PROVEN
RH_NOT_PROVEN
AUTHORITY_EFFECT_NONE
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators

set_option autoImplicit false

noncomputable section

namespace AEGIS.WeilWindowExhaustionV1

open AEGIS.WeilLogCoordinateIsometryV21

/-- Compact x-support mapped into logarithmic coordinates. -/
def logSupportEnvelopeV1 (g : WeilCompactSmoothGV1) : Set ℝ :=
  Real.log '' tsupport g.1

/-- The logarithmic support envelope is compact because repository packet
support is compact and lies strictly inside the positive half-line. -/
theorem logSupportEnvelope_compact_v1 (g : WeilCompactSmoothGV1) :
    IsCompact (logSupportEnvelopeV1 g) := by
  apply g.2.2.1.image_of_continuousOn
  exact Real.continuousOn_log.mono (by
    intro x hx
    have hx0 : x ≠ 0 := (g.2.2.2 hx).ne'
    simpa using hx0)

/-- The actual topological support of the logarithmic lift lies in the compact
logarithmic image of the original packet support. -/
theorem logLift_tsupport_subset_envelope_v1 (g : WeilCompactSmoothGV1) :
    tsupport (logLift g.1) ⊆ logSupportEnvelopeV1 g := by
  apply closure_minimal ?_ (logSupportEnvelope_compact_v1 g).isClosed
  intro t ht
  by_contra hnot
  apply ht
  unfold logLift
  have hg : g.1 (Real.exp t) = 0 := by
    by_contra hgne
    apply hnot
    refine ⟨Real.exp t, subset_tsupport _ hgne, ?_⟩
    exact Real.log_exp t
  simp [hg]

/-- A finite symmetric logarithmic window containing the lifted support. -/
def LogWindowContainsV1 (g : WeilCompactSmoothGV1) (L : ℝ) : Prop :=
  tsupport (logLift g.1) ⊆ Icc (-L) L

/-- Every repository test packet belongs to some finite positive log window. -/
theorem logLift_has_finite_window_v1 (g : WeilCompactSmoothGV1) :
    ∃ L : ℝ, 0 < L ∧ LogWindowContainsV1 g L := by
  obtain ⟨L, hL, hsub⟩ :=
    (logSupportEnvelope_compact_v1 g).isBounded.subset_closedBall_lt (0 : ℝ) 0
  refine ⟨L, hL, ?_⟩
  intro t ht
  have hball := hsub (logLift_tsupport_subset_envelope_v1 g ht)
  have habs : |t| ≤ L := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hball
  exact abs_le.mp habs

/-- Arithmetic nonpositivity restricted to one finite symmetric log window. -/
def WindowArithmeticNonpositiveV1 (L : ℝ) : Prop :=
  ∀ g : WeilCompactSmoothGV1,
    WeilMomentConditionsV1 g →
    LogWindowContainsV1 g L →
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0

/-- Existing unrestricted arithmetic sign obligation, named locally only to
state the exhaustion equivalence without changing repository semantics. -/
def UniversalArithmeticNonpositiveV1 : Prop :=
  ∀ g : WeilCompactSmoothGV1,
    WeilMomentConditionsV1 g →
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0

/-- The full compact-support sign problem is exactly the family of all finite
log-window sign problems. No approximation or limit passage is used: each
compactly supported packet already lives in one finite window. -/
theorem universal_arithmetic_nonpositive_iff_all_windows_v1 :
    UniversalArithmeticNonpositiveV1 ↔
      ∀ L : ℝ, 0 < L → WindowArithmeticNonpositiveV1 L := by
  constructor
  · intro h L hL g hm hwindow
    exact h g hm
  · intro h g hm
    obtain ⟨L, hL, hwindow⟩ := logLift_has_finite_window_v1 g
    exact h L hL g hm hwindow

/-- Bind the exhaustion theorem directly to the repository's existing
compact-smooth Weil-negativity predicate. -/
theorem weil_compact_smooth_negativity_iff_all_windows_v1 :
    WeilCompactSmoothNegativityV1 ↔
      ∀ L : ℝ, 0 < L → WindowArithmeticNonpositiveV1 L := by
  rw [weil_compact_smooth_negativity_iff_unconditional_real_inequality_v1]
  exact universal_arithmetic_nonpositive_iff_all_windows_v1

/-- Larger windows imply all smaller-window sign obligations. -/
theorem windowArithmeticNonpositive_mono_v1
    {L₁ L₂ : ℝ} (hL : L₁ ≤ L₂)
    (h : WindowArithmeticNonpositiveV1 L₂) :
    WindowArithmeticNonpositiveV1 L₁ := by
  intro g hm hwindow
  apply h g hm
  intro t ht
  have hI := hwindow ht
  exact ⟨by linarith [hI.1], by linarith [hI.2]⟩

/-- The continuum of positive real windows is equivalent to the cofinal
countable sequence of positive integer windows. -/
theorem all_windows_iff_positive_nat_windows_v1 :
    (∀ L : ℝ, 0 < L → WindowArithmeticNonpositiveV1 L) ↔
      ∀ n : ℕ, 0 < n → WindowArithmeticNonpositiveV1 (n : ℝ) := by
  constructor
  · intro h n hn
    exact h (n : ℝ) (by exact_mod_cast hn)
  · intro h L hL
    obtain ⟨n, hn⟩ := exists_nat_gt L
    have hnR : (0 : ℝ) < (n : ℝ) := hL.trans hn
    have hnNat : 0 < n := by exact_mod_cast hnR
    exact windowArithmeticNonpositive_mono_v1 (le_of_lt hn) (h n hnNat)

/-- Final countable exhaustion form of the existing repository negativity
predicate. The remaining analytic target can therefore be indexed by positive
natural window radii, with no loss of logical strength. -/
theorem weil_compact_smooth_negativity_iff_positive_nat_windows_v1 :
    WeilCompactSmoothNegativityV1 ↔
      ∀ n : ℕ, 0 < n → WindowArithmeticNonpositiveV1 (n : ℝ) := by
  rw [weil_compact_smooth_negativity_iff_all_windows_v1]
  exact all_windows_iff_positive_nat_windows_v1

end AEGIS.WeilWindowExhaustionV1

#print axioms AEGIS.WeilWindowExhaustionV1.logSupportEnvelope_compact_v1
#print axioms AEGIS.WeilWindowExhaustionV1.logLift_tsupport_subset_envelope_v1
#print axioms AEGIS.WeilWindowExhaustionV1.logLift_has_finite_window_v1
#print axioms AEGIS.WeilWindowExhaustionV1.universal_arithmetic_nonpositive_iff_all_windows_v1
#print axioms AEGIS.WeilWindowExhaustionV1.weil_compact_smooth_negativity_iff_all_windows_v1
#print axioms AEGIS.WeilWindowExhaustionV1.windowArithmeticNonpositive_mono_v1
#print axioms AEGIS.WeilWindowExhaustionV1.all_windows_iff_positive_nat_windows_v1
#print axioms AEGIS.WeilWindowExhaustionV1.weil_compact_smooth_negativity_iff_positive_nat_windows_v1
