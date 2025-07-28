/-
Copyright 2025 The Formal Conjectures Authors.

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
# Littlewood conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Littlewood_conjecture)
-/

open Filter

-- TODO(mercuris): This is a norm on ℝ/ℤ, show this?
/--
The distance to the nearest integer is the function
$\||x\|| := \min(|x - \lfloor x \rfloor|, |x - \lceil x \rceil|)$.
-/
noncomputable abbrev distToNearestInt (x : ℝ) : ℝ := |x - round x|

/--
For any two real numbers $\alpha$ and $\beta$,
$$
  \liminf_{n\to\infty} n\||n\alpha\||\||n\beta\|| = 0
$$
where $\||nx\|| := \min(|x - \lfloor x \rfloor|, |x - \lceil x \rceil|)$ is the distance
to the nearest integer.
-/
@[category research solved, AMS 11]
theorem littlewood_conjecture (α β : ℝ) :
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0 := by
  sorry

section MatrixGroupConjecture

open Matrix
open scoped MatrixGroups

section
variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]


private def Matrix.diagonalHom : (n → Rˣ) →* GeneralLinearGroup n R where
  toFun := fun d ↦ ⟨Matrix.diagonal (fun i ↦ d i), Matrix.diagonal (fun i ↦ (d i).inv), by simp, by simp⟩
  map_mul' x y := by ext; simp [-mul_diagonal, -diagonal_mul]
  map_one' := by ext; simp

/-- The group of invertible diagonal matrices. -/
private def DiagonalMatricesMultiplicative : Subgroup (GeneralLinearGroup n R) :=
  Subgroup.map (Matrix.diagonalHom n R) ⊤

/-- The group of invertible diagonal matrices with determinant 1. -/
private def SpecialDiagonalMatrices : Subgroup (SpecialLinearGroup n R) :=
  (DiagonalMatricesMultiplicative n R).comap Matrix.SpecialLinearGroup.toGL

-- TODO(Paul-Lez): do we want to upstream this to Mathlib?
instance : TopologicalSpace (SpecialLinearGroup n ℝ) :=
  inferInstanceAs (TopologicalSpace { A : Matrix n n ℝ // A.det = 1 })

variable {n R} in
def Matrix.SpecialLinearGroup.coeIntGroupHom : SpecialLinearGroup n ℤ →* SpecialLinearGroup n R where
  toFun x := ↑x
  map_mul' := by simp
  map_one' := by simp

end

/-- Let `n ≥ 3`, `G = SL_n(ℝ)` and `Γ = SL_(ℤ)`, and the subgroup `D` of diagonal matrices in `G`.

Conjecture: for any `g` in `G/Γ` such that `Dg` is relatively compact (in `G/Γ`), then `Dg` is closed.-/
@[category research open]
theorem matrix_group_conjecture {n : ℕ} (hm : 3 ≤ n) (g : SL(n, ℝ))
    (Dg : Set (SL(n, ℝ) ⧸ (⊤ : Subgroup _).map Matrix.SpecialLinearGroup.coeIntGroupHom))
    (Dg_def : Dg = { QuotientGroup.mk (d * g) | (d : SL(n, ℝ)) (_ : d ∈ SpecialDiagonalMatrices _ _) })
    (hg : IsCompact <| closure Dg) :
    IsClosed Dg :=
  sorry

end MatrixGroupConjecture
