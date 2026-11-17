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
THE COMPLEX GROTHENDIECK CONSTANT](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-haagerup/1980s/1987_A_new_upper_bound_for_the_complex_Grothendieck_constant.pdf) by *U. Haagerup* (1987)
[Grothendieck's Constant](https://mathworld.wolfram.com/GrothendiecksConstant.html)


Let `m ∈ ℕ` and `A` be a complex `m × m` matrix such that for all complex numbers `s 1,...,s m` and `t 1,...,t m` satisfying `|s i|, |t j|≤ 1` it holds `|∑ (A i j) * (s j) * (t j)| ≤ 1`.
Let `n ∈ ℕ` and `x 1,...,x m` and `y 1,...,y m` be complex vectors in `ℂ ^ n` with `‖x i‖ , ‖y j‖ ≤ 1`.
The complex Grothendieck constant `KGC` is the smallest number independent of `n` and `m` for which  `|∑ (A i j) * ⟪x i, y j⟫_ℂ| ≤ KGC` for every such matrix `A` and all such vectors `x i, y j`.

In the reference paper [Haa87] Haagerup doubted that his upper bound is the exact value of `KGC` and proposed the smaller candidate `1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`

Recent progress [HJM26] showed `1.4 < KGC < 1.404898554746`. Haagerup's candidate lies in between these bounds.

*Remark:* Shifting to 0 indexing in this formalization to follow lean conventions.
The formulation in [Grothendieck's Constant] asks for `m` and `n` to be positive integers. However, them being zero leads to trivial cases, so allowing `m n : ℕ` is an equivalent formulation, which is used here for simplicity.

## References

- [Gro53] A. Grothendieck, Résumé de la théorie métrique des produits tensoriels topologiques, Bol. Soc. Mat. São Paulo 8 (1953), 1-79
- [Haa87] U. Haagerup, A new upper bound for the complex Grothendieck constant, Israel J. Math. 60 (1987), 199–224.
- [HJM26] Sharper Bounds for the Complex Grothendieck Constant, arXiv:2609.25462 [math.FA]
- [Pis12] G. Pisier, Grothendieck’s theorem, past and present, Bull. Amer. Math. Soc. 49 (2012), 237-323
-/

@[expose] public section

namespace ComplexGrothendieckConstant

open Complex
open scoped InnerProductSpace
open Matrix

/--
The type of complex valued `m×m` square matrices.

Abbreviation of `Matrix (Fin m) (Fin m) ℂ`.
-/
abbrev CSqMat (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

/--
The matrix property that appears in the complex Grothendieck inequality.
-/
def HasMatrixProperty {m : ℕ} (A : CSqMat m) : Prop :=
  ∀ s t : Fin m → ℂ,
    ((∀ i, ‖s i‖ ≤ 1) ∧ (∀ j, ‖t j‖ ≤ 1)) →
      ‖∑ i, ∑ j, A i j * s i * t j‖ ≤ 1

/--
The statement that `K` satisfies the complex Grothendieck inequality in every dimension.
-/
def IsUniversalConstant (K : ℝ) : Prop :=
  ∀ m n : ℕ, ∀ A : CSqMat m, HasMatrixProperty A →
    ∀ x y : Fin m → EuclideanSpace ℂ (Fin n),
      ((∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1)) →
        ‖∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℂ‖ ≤ K

/--
There exists a finite bound in the Grothendieck inequality that is universal in dimension.
This can be quickly deduced from the real bound established in [Gro53], see [Pis12].
-/
@[category research solved, AMS 42 46 47]
theorem exists_universal_constant :
  ∃ K : ℝ, IsUniversalConstant K := by sorry

/--
The statement that `KGC`is exactly the complex Grothendieck Constant. There exists a unique such constant, since the supremum is bounded by the constant established in `exists_universal_constant`.
-/
def IsKGC (KGC : ℝ) : Prop :=
  IsUniversalConstant KGC ∧
    ∀ K, IsUniversalConstant K → KGC ≤ K


noncomputable def haagerup_candidate.answer : ℝ :=
  (∫ θ in (0:ℝ)..(Real.pi / 2),
    Real.cos θ ^ 2 / √(1 + Real.sin θ ^ 2))⁻¹

/--
The complex Grothendieck Constant equals `1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`.

This was proposed as "sensible candidate" by Haagerup in [Haa87].
-/
@[category research open, question value, AMS 42 46 47]
theorem haagerup_candidate : IsKGC haagerup_candidate.answer := by
  sorry

end ComplexGrothendieckConstant
