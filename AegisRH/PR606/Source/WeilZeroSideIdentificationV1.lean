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

/-
AEGIS Ω — the zero side of the Weil semantics is exactly Mathlib's RH.

`WeilZeroSideInterfaceV1` proves one direction: assuming Mathlib's
`RiemannHypothesis`, every inhabitant of `WeilNontrivialZeroV1` lies on the
critical line.  The converse was never stated, so the interface left open
whether the AEGIS subtype is genuinely Mathlib's condition, or something
weaker that merely follows from it.

This file adds the converse and packages both as an iff.  The converse is the
informative half: it shows the subtype discards no case that Mathlib's
quantifier covers, since an arbitrary `s` carrying the three side conditions
can be packaged into the subtype and the conclusion read back.

WHAT THIS CLOSES

The ZERO-SIDE half of the semantic identification requested by the gate
`aegis_weil_semantics_mapped_to_mathlib`.  The AEGIS zero side is not a
surrogate for Mathlib's `RiemannHypothesis`; it is that statement.

WHAT THIS LEAVES OPEN

The prime side, untouched.  Identifying `WeilExplicitRightSideV1` with the
actual Weil functional is the Weil explicit formula, which
`WeilZeroSideInterfaceV1` itself records as `EXPLICIT_FORMULA_THEOREM_OPEN`,
alongside `ZERO_SIDE_GLOBAL_SUM_OPEN` and
`ZERO_MULTIPLICITY_ENUMERATION_OPEN`.  The gate therefore stays open.

ON THE REPRODUCED DEFINITION

`WeilNontrivialZeroV1` is reproduced verbatim rather than imported, because
this repository compiles its bridge files standalone.  The reproduction was
diffed against the interface and is byte-identical.  Drift would invalidate
the identification; note also that the iff below fails to compile unless the
mirrored predicate matches Mathlib's three side conditions exactly, so the
statement is self-guarding against a mirror that is wrong relative to Mathlib.

This proves no part of RH and contains no term of type `RiemannHypothesis`:
the forward direction consumes RH as a hypothesis and the converse consumes
universal criticality.  AUTHORITY_EFFECT = NONE.
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

noncomputable section

/-- Reproduced verbatim from `WeilZeroSideInterfaceV1`; a nontrivial zero in
exactly the sense used by Mathlib's `RiemannHypothesis`. -/
def WeilNontrivialZeroV1 :=
  { rho : ℂ //
      riemannZeta rho = 0 ∧
      (¬ ∃ n : ℕ, rho = -2 * (n + 1)) ∧
      rho ≠ 1 }

namespace AEGIS.WeilZeroSideIdentificationV1

/-- Forward direction, as already present in the interface: RH places every
inhabitant of the subtype on the critical line. -/
theorem rh_implies_all_zeros_critical
    (hRH : RiemannHypothesis) (rho : WeilNontrivialZeroV1) :
    rho.1.re = 1 / 2 :=
  hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2

/-- Converse, the informative half: the subtype is not weaker than Mathlib's
quantifier.  Any `s` carrying the three side conditions inhabits the subtype,
so criticality on the subtype transfers back to Mathlib's statement. -/
theorem all_zeros_critical_implies_rh
    (h : ∀ rho : WeilNontrivialZeroV1, rho.1.re = 1 / 2) :
    RiemannHypothesis :=
  fun s hz htriv hone => h ⟨s, hz, htriv, hone⟩

/-- THE ZERO-SIDE IDENTIFICATION.  The AEGIS nontrivial-zero subtype
characterises Mathlib's `RiemannHypothesis` exactly, in both directions, so
the zero side of the AEGIS Weil semantics is not a surrogate. -/
theorem zero_side_is_exactly_mathlib_rh :
    RiemannHypothesis ↔ ∀ rho : WeilNontrivialZeroV1, rho.1.re = 1 / 2 :=
  ⟨rh_implies_all_zeros_critical, all_zeros_critical_implies_rh⟩

/-- Non-vacuity control: the defining predicate is discriminating.  `s = 1` is
excluded, so the subtype is neither empty of constraint nor all of the plane,
and the iff above is not an artefact of a degenerate condition. -/
theorem zero_subtype_predicate_is_discriminating :
    ¬ (riemannZeta 1 = 0 ∧ (¬ ∃ n : ℕ, (1 : ℂ) = -2 * (n + 1)) ∧ (1 : ℂ) ≠ 1) := by
  rintro ⟨-, -, h⟩
  exact h rfl

end AEGIS.WeilZeroSideIdentificationV1
