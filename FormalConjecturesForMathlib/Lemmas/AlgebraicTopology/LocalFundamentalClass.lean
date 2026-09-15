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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.LocalFundamentalClass

/-!
# A standard local fundamental cycle

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.LocalFundamentalClass`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

attribute [fun_prop] stdSimplex.continuous_map

lemma standardAffineSimplex_eq_zero_iff (d : ℕ)
    (t : stdSimplex ℝ (Fin (d + 1))) :
    standardAffineSimplex d t = 0 ↔ t = stdSimplex.barycenter := by
  constructor
  · intro h
    have hcoord (j : Fin d) : t (Fin.castSucc j) = t (Fin.last d) := by
      have hj := congr_fun h j
      simpa [standardAffineSimplex] using sub_eq_zero.mp hj
    have hall (j : Fin (d + 1)) : t j = t (Fin.last d) := by
      rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
      · exact hcoord k
      · rfl
    have hsum : ∑ _ : Fin (d + 1), t (Fin.last d) = 1 := by
      rw [← t.2.2]
      exact Finset.sum_congr rfl fun j _ => (hall j).symm
    have hcard : (Fintype.card (Fin (d + 1)) : ℝ) ≠ 0 := by
      simp only [Fintype.card_fin]
      positivity
    have hlast : t (Fin.last d) = (Fintype.card (Fin (d + 1)) : ℝ)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
      exact ((mul_eq_one_iff_inv_eq₀ hcard).mp hsum).symm
    apply stdSimplex.ext
    funext j
    rw [hall j, hlast]
    exact stdSimplex.barycenter_apply j |>.symm
  · rintro rfl
    ext j
    change (stdSimplex.barycenter : stdSimplex ℝ (Fin (d + 1)))
      (Fin.castSucc j) - stdSimplex.barycenter (Fin.last d) = 0
    exact sub_self _

lemma standardLocalCycle_inclusion (d : ℕ) :
    standardLocalCycle d ≫ (standardLocalRelativeChainComplex d).iCycles d =
      standardLocalChain d :=
  (standardLocalRelativeChainComplex d).liftCycles_i (standardLocalChain d)
    ((ComplexShape.down ℕ).next d) rfl (standardLocalChain_boundary d)

end AlgebraicTopology.Singular
