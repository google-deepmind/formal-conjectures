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
module

public import FormalConjecturesUtil

/-!
# Knill's Question B: maximal Green eigenvalue

*References:*
- [O. Knill, Remarks about Connection and Dirac matrices, version 2, Sections 1.4 and 10.2, Question B](https://arxiv.org/html/2601.18071v2)
- [J. J. Gebendorfer, Odd Cycles and the Maximal Green Eigenvalue of Connection Matrices, 9 August 2026; manuscript archive](https://github.com/user-attachments/files/33368337/Knill_Intake_Gebendorfer_2026-10-13.zip)

The target is simplicity of the largest ALGEBRAIC eigenvalue of the inverse
connection matrix. It is not simplicity of the spectral-radius eigenvalue;
Question C and the greatest-absolute-value variant are separate.
-/

@[expose] public section
namespace Knill.GreenEigenvalue

/-- Connection matrix indexed by the nonempty faces of the actual complex. -/
noncomputable def connectionMatrix (n : ℕ)
    (K : PreAbstractSimplicialComplex (Fin n)) :
    Matrix {σ : Finset (Fin n) // σ ∈ K} {σ : Finset (Fin n) // σ ∈ K} ℝ := by
  classical
  exact fun σ τ => if Disjoint σ.val τ.val then 0 else 1

/-- Algebraic multiplicity of the largest real Green eigenvalue. The existing
abstract-complex type enforces nonempty faces and downward closure. Finiteness
follows from the finite vertex set, without restricting the dimension. -/
noncomputable def maximalMultiplicity (n : ℕ)
    (K : PreAbstractSimplicialComplex (Fin n)) : ℕ := by
  classical
  letI := Fintype.ofFinite {σ : Finset (Fin n) // σ ∈ K}
  let g := (connectionMatrix n K)⁻¹
  exact g.charpoly.rootMultiplicity (sSup (spectrum ℝ g))

/-- The largest algebraic eigenvalue of the Green matrix is not always simple
on finite nonempty abstract simplicial complexes. The written counterfamily is
formed by the one-dimensional odd cycle complexes; no minimum-order claim is
included in this universal negative answer. -/
@[question, category research solved, AMS 5 15]
theorem questionB : ¬ ∀ (n : ℕ) (K : PreAbstractSimplicialComplex (Fin n)),
    K.faces.Nonempty → maximalMultiplicity n K = 1 := by
  sorry

end Knill.GreenEigenvalue
