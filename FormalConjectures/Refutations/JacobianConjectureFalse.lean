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

import FormalConjectures.Wikipedia.JacobianConjecture

/-!
# The Jacobian Conjecture is false (n = 3, over ℚ)

CLAIM-TYPING — read before citing this file:

* The counterexample map is **NOT ours**. It is Levent Alpöge's (announced 2026-07-19, found with
  Claude Fable; question credited to Akhil). At the time of writing it is "awaiting confirmation":
  widely verified, but not peer-reviewed. If the map were ever retracted this file would prove
  nothing about the Jacobian Conjecture — only things about the specific polynomials below.
* What this file contributes is a machine-checked proof, against the statement in
  `FormalConjectures/Wikipedia/JacobianConjecture.lean` (restated verbatim below so the goalposts
  are the community's, not ours), that the conjecture as stated is FALSE for `k = ℚ`, `σ = Fin 3`.
* The two facts doing the work are `alpoge_jacobian_det` (`det J_F = C (-2)`) and
  `alpoge_collision` (`F` identifies two distinct rational points). Everything else is plumbing.
* `sorry`-free — see `#print axioms jacobian_conjecture_false` at the bottom.
-/

namespace JacobianConjecture

open MvPolynomial RegularFunction

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section

/-- Coordinates on `𝔸³` over `ℚ`. -/
noncomputable abbrev xx : MvPolynomial (Fin 3) ℚ := X 0
noncomputable abbrev yy : MvPolynomial (Fin 3) ℚ := X 1
noncomputable abbrev zz : MvPolynomial (Fin 3) ℚ := X 2

/-- **Alpöge's Keller map** `F : 𝔸³ → 𝔸³` (2026): Jacobian determinant identically `-2`,
yet not injective. -/
noncomputable def alpoge : RegularFunction ℚ (Fin 3) (Fin 3) :=
  ![ (1 + xx * yy) ^ 3 * zz + yy ^ 2 * (1 + xx * yy) * (4 + 3 * xx * yy),
     yy + 3 * xx * (1 + xx * yy) ^ 2 * zz + 3 * xx * yy ^ 2 * (4 + 3 * xx * yy),
     2 * xx - 3 * xx ^ 2 * yy - xx ^ 3 * zz ]

/-- A derivation kills numeric literals. Needed because the constants `3` and `4` in the map are
`OfNat` literals rather than `C _`, so `pderiv_C` does not fire on them; `no_index` is required or
`simp`'s discrimination tree will not match the literal. -/
@[simp, category API, AMS 14]
lemma pderiv_ofNat_mv (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    (pderiv i) (no_index (OfNat.ofNat n) : MvPolynomial (Fin 3) ℚ) = 0 := by
  rw [← map_ofNat (C : ℚ →+* MvPolynomial (Fin 3) ℚ) n, pderiv_C]

/- ### The nine partial derivatives

Each is a small goal, so `simp` can compute the derivative (the `pderiv` lemmas are `@[simp]`)
and `ring` matches it to the explicit form. Splitting them keeps `simp` off the huge
determinant expression, where it does not terminate. (`try ring` because `simp` alone already
closes the easier ones.) -/

@[category API, AMS 14]
lemma d1_f1 : pderiv 0 (alpoge 0)
    = 3 * (1 + xx*yy)^2 * yy * zz + yy^3 * (4 + 3*xx*yy) + 3 * (1 + xx*yy) * yy^3 := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d2_f1 : pderiv 1 (alpoge 0)
    = 3 * (1 + xx*yy)^2 * xx * zz + 2*yy*(1 + xx*yy)*(4 + 3*xx*yy)
      + xx*yy^2*(4 + 3*xx*yy) + 3*xx*(1 + xx*yy)*yy^2 := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d3_f1 : pderiv 2 (alpoge 0) = (1 + xx*yy)^3 := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d1_f2 : pderiv 0 (alpoge 1)
    = 3*(1 + xx*yy)^2*zz + 6*xx*(1 + xx*yy)*yy*zz + 3*yy^2*(4 + 3*xx*yy) + 9*xx*yy^3 := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d2_f2 : pderiv 1 (alpoge 1)
    = 1 + 6*xx^2*(1 + xx*yy)*zz + 6*xx*yy*(4 + 3*xx*yy) + 9*xx^2*yy^2 := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d3_f2 : pderiv 2 (alpoge 1) = 3*xx*(1 + xx*yy)^2 := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d1_f3 : pderiv 0 (alpoge 2) = 2 - 6*xx*yy - 3*xx^2*zz := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d2_f3 : pderiv 1 (alpoge 2) = -(3*xx^2) := by
  simp [alpoge]; try ring

@[category API, AMS 14]
lemma d3_f3 : pderiv 2 (alpoge 2) = -(xx^3) := by
  simp [alpoge]; try ring

/- ### The two load-bearing facts -/

/-- The Jacobian determinant of Alpöge's map is the nonzero constant `-2`. -/
@[category API, AMS 14]
lemma alpoge_jacobian_det : alpoge.Jacobian.det = C (-2 : ℚ) := by
  rw [Matrix.det_fin_three]
  simp only [RegularFunction.Jacobian, Matrix.of_apply,
    d1_f1, d2_f1, d3_f1, d1_f2, d2_f2, d3_f2, d1_f3, d2_f3, d3_f3]
  have hC : (C (-2 : ℚ) : MvPolynomial (Fin 3) ℚ) = -2 := by simp [map_ofNat]
  rw [hC]
  ring

/-- Hence Alpöge's map satisfies the conjecture's hypothesis. -/
@[category API, AMS 14]
lemma alpoge_jacobian_isUnit : IsUnit alpoge.Jacobian.det := by
  rw [alpoge_jacobian_det]
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (-2 : ℚ) ≠ 0)).map
    (C : ℚ →+* MvPolynomial (Fin 3) ℚ)

/-- Two distinct rational points. -/
def P : Fin 3 → ℚ := ![0, 0, -1/4]
/-- ... the second of the colliding pair. -/
def Q : Fin 3 → ℚ := ![1, -3/2, 13/2]

@[category API, AMS 14]
lemma P_ne_Q : P ≠ Q := fun h => by
  have h0 := congrFun h 0
  simp [P, Q] at h0

/-- Alpöge's map identifies `P` and `Q` (both land on `(-1/4, 0, 0)`): it is not injective. -/
@[category API, AMS 14]
lemma alpoge_collision :
    RegularFunction.aeval (S₁ := ℚ) alpoge P = RegularFunction.aeval (S₁ := ℚ) alpoge Q := by
  funext i
  fin_cases i <;> simp [RegularFunction.aeval, alpoge, P, Q] <;> norm_num

/-- Evaluating the identity regular function is the identity on points. -/
@[category API, AMS 14]
lemma aeval_id (a : Fin 3 → ℚ) :
    RegularFunction.aeval (S₁ := ℚ) (RegularFunction.id ℚ (Fin 3)) a = a := by
  funext t
  simp [RegularFunction.aeval, RegularFunction.id]

/-- A regular right inverse forces the underlying point map to be injective. -/
@[category API, AMS 14]
lemma injective_of_comp_id {F G : RegularFunction ℚ (Fin 3) (Fin 3)}
    (h : F.comp G = RegularFunction.id ℚ (Fin 3)) :
    Function.Injective (RegularFunction.aeval (S₁ := ℚ) F) := by
  have key : ∀ a, RegularFunction.aeval (S₁ := ℚ) G (RegularFunction.aeval (S₁ := ℚ) F a) = a := by
    intro a
    have hc := comp_aeval F G a
    rw [h, aeval_id] at hc
    exact hc.symm
  intro a b hab
  rw [← key a, hab, key b]

/- ### The refutation -/

/-- **The Jacobian Conjecture is false.**

The statement is copied verbatim from `JacobianConjecture.jacobian_conjecture` (same
`RegularFunction`, `Jacobian`, `comp`, `id`), specialised to `k = ℚ` and `σ = Fin 3`. -/
@[category research solved, AMS 14]
theorem jacobian_conjecture_false :
    ¬ ∀ (F : RegularFunction ℚ (Fin 3) (Fin 3)), IsUnit F.Jacobian.det →
        ∃ G : RegularFunction ℚ (Fin 3) (Fin 3),
          G.comp F = RegularFunction.id ℚ (Fin 3) ∧
          F.comp G = RegularFunction.id ℚ (Fin 3) := by
  intro hJC
  obtain ⟨G, -, hFG⟩ := hJC alpoge alpoge_jacobian_isUnit
  exact P_ne_Q (injective_of_comp_id hFG alpoge_collision)

-- Axiom audit: this must report ONLY Lean's three standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`). Any `sorryAx` means the proof is incomplete.
#print axioms jacobian_conjecture_false

end

end JacobianConjecture
