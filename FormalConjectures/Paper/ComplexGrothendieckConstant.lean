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
# Haagerup Candidate for Complex Grothendieck Constant

*Reference:* [A NEW UPPER BOUND FOR
THE COMPLEX GROTHENDIECK CONSTANT](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-haagerup/1980s/1987_A_new_upper_bound_for_the_complex_Grothendieck_constant.pdf)
[Grothendieck's Constant](https://mathworld.wolfram.com/GrothendiecksConstant.html)


Let `m ∈ ℕ` a positive integer and `A` be a complex `m×m` matrix such that for all complex numbers `s 1,...,s m` and `t 1,...,t m` satisfying `|s i|, |t j|≤ 1` it holds `|∑ (A i j)(s j)(t j)| ≤ 1`.
Let `n ∈ ℕ` a positive integer and `x 1,...,x m` and `y 1,...,y m` be complex vectors in `ℂ ^ n` with `‖x i‖ , ‖y j‖ ≤ 1`.
The complex Grothendieck constant `KGC` is the smallest number independent of `n` and `m` for which  `|∑ (A i j) * (x i) ⬝ᵥ (y j)| ≤ KGC` for every such matrix `A` and all such vectors `x i, y j`.

In the reference paper Haagerup doubted that his upper bound is the exact value of `KGC` and proposed the smaller candidate `1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ))`

*Remark:* Shifting to 0 indexing in this formalization to follow lean conventions.
-/

@[expose] public section

namespace ComplexGrothendieckConstant

open Complex
open scoped InnerProductSpace
open Matrix

/--
A complex valued m×m square matrix
-/
abbrev CSqMat (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

/--
The matrix property that appears in the Grothendieck inequality
-/
def HasMatrixProperty {m : ℕ} (A : CSqMat m) : Prop :=
  ∀ s t : Fin m → ℂ,
    ((∀ i, ‖s i‖ ≤ 1) ∧ (∀ j, ‖t j‖ ≤ 1)) →
      ‖∑ i, ∑ j, A i j * s i * t j‖ ≤ 1

def IsUniversalConstant (K : ℝ) : Prop :=
  ∀ m n : ℕ, ∀ A : CSqMat m, HasMatrixProperty A →
    ∀ x y : Fin m → EuclideanSpace ℂ (Fin n),
      ((∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1)) →
        ‖∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℂ‖ ≤ K

def IsKGC (KGC : ℝ) : Prop :=
  IsUniversalConstant KGC ∧
    ∀ K, IsUniversalConstant K → KGC ≤ K

@[category research solved, AMS 42 46 47]
theorem exists_universal_constant :
  ∃ K : ℝ, IsUniversalConstant K := by sorry

noncomputable def haagerup.answer : ℝ :=
  (∫ θ in (0:ℝ)..(Real.pi / 2),
    Real.cos θ ^ 2 / √(1 + Real.sin θ ^ 2))⁻¹

@[category research open, question value, AMS 42 46 47]
theorem haagerup : IsKGC haagerup.answer := by
  sorry

end ComplexGrothendieckConstant
