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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 114

*Reference:* [erdosproblems.com/114](https://www.erdosproblems.com/114)

The **Erdős--Herzog--Piranian lemniscate-length conjecture** asks whether,
among monic complex polynomials of degree `n`, the lemniscate
`{z : ℂ | ‖p.eval z‖ = 1}` has maximal length for `p = X ^ n - C 1`.

The all-degree conjecture remains open.  The finite statement below records
the current certificate-backed range `1 ≤ n ≤ 14`: degree `1` is elementary,
degree `2` follows from the Eremenko--Hayman treatment, and degrees `3`
through `14` are supported by the Mendoza finite-degree certificate packet.
The Lean statements here do not formalize those external certificates.

### References

- [EHP58] Erdős, P., Herzog, F., Piranian, G. (1958). *Metric properties of
  polynomials*. J. Analyse Math. 6, 125--148.
- [EH99] Eremenko, A., Hayman, W. (1999). *On the length of lemniscates*.
  Michigan Math. J. 46, 409--415.
- [Po61] Pommerenke, Ch. (1961). *Uber die Kapazitat ebener Kontinuen*.
  Math. Ann. 144, 115--120.
- [Ta25] Tao, T. (2025). *The Erdős--Herzog--Piranian conjecture for large n*.
- [Me26] Mendoza, K. A. (2026). *Finite-degree verification for the
  Erdős--Herzog--Piranian lemniscate-length conjecture*.
  doi:10.5281/zenodo.19184467.
  Source release: https://github.com/MendozaLab/erdos-experiments/releases/tag/v3.1.0.

### AI disclosure

Lean 4 code in this file was drafted with AI assistance.  The mathematical
content, external certificate packet, and references are the contributor's
responsibility.
-/

open Polynomial MeasureTheory ENNReal Classical

namespace Erdos114

/-- The level-1 lemniscate of a complex polynomial `p`. -/
def levelCurveUnit (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ = 1}

/-- The length of a subset of `ℂ`, represented as its one-dimensional
Hausdorff measure. -/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ :=
  μH[1] s

/-- The length of the level-1 lemniscate of `p`. -/
noncomputable def lemniscateLength (p : ℂ[X]) : ℝ≥0∞ :=
  length (levelCurveUnit p)

/-- **Erdős Problem 114** (open conjecture).  Among monic complex polynomials
of degree `n`, `X ^ n - C 1` maximizes the length of the level-1 lemniscate.

This is the all-degree conjecture and remains open. -/
@[category research open, AMS 30]
theorem erdos_114 (n : ℕ) (hn : 1 ≤ n)
    (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    lemniscateLength p ≤ lemniscateLength (X ^ n - C (1 : ℂ)) := by
  sorry

/-- **Finite-degree EHP certificate range.**  For `1 ≤ n ≤ 14`, the polynomial
`X ^ n - C 1` maximizes the length of the level-1 lemniscate among monic
complex polynomials of exact degree `n`.

This statement records a finite, externally certificate-backed result: `n = 1`
is elementary, `n = 2` follows from the Eremenko--Hayman treatment, and
`3 ≤ n ≤ 14` is supported by the Mendoza 2026 IEEE-1788 interval certificate
packet.  The external certificate pipeline is not formalized in this Lean file,
so the proof remains a `sorry` rather than an imported axiom. -/
@[category research solved, AMS 30]
theorem erdos_114_finite_le_14 (n : ℕ) (hn : 1 ≤ n) (hn14 : n ≤ 14)
    (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    lemniscateLength p ≤ lemniscateLength (X ^ n - C (1 : ℂ)) := by
  sorry

end Erdos114
