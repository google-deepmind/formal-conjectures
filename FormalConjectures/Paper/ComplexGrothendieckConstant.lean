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
by *U. Haagerup* (1987)
[Grothendieck's Constant](https://mathworld.wolfram.com/GrothendiecksConstant.html)


Let `m ∈ ℕ` and `A` be a complex `m × m` matrix such that for all complex numbers `s 1,...,s m`
and `t 1,...,t m` satisfying `|s i|, |t j|≤ 1` it holds `|∑ (A i j) * (s i) * (t j)| ≤ 1`.
Let `n ∈ ℕ` and `x 1,...,x m` and `y 1,...,y m` be complex vectors in `ℂ ^ n` with
`‖x i‖ , ‖y j‖ ≤ 1`. The complex Grothendieck constant `KGC` is the smallest number independent
of `n` and `m` for which  `|∑ (A i j) * ⟪x i, y j⟫_ℂ| ≤ KGC` for every such matrix `A` and all
such vectors `x i, y j`.

In the reference paper [Haa87] Haagerup doubted that his upper bound is the exact value of `KGC`
and proposed the smaller candidate `1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`

Recent progress [HJM26] showed `1.4 < KGC < 1.404898554746`. Haagerup's candidate lies in between
these bounds.

*Remark:* Shifting to 0 indexing in this formalization to follow lean conventions.
The formulation in [Grothendieck's Constant] asks for `m` and `n` to be positive integers.
However, them being zero leads to trivial cases, so allowing `m n : ℕ` is an equivalent
formulation, which is used here for simplicity.

## References

- [Gro53] A. Grothendieck, Résumé de la théorie métrique des produits tensoriels topologiques,
  Bol. Soc. Mat. São Paulo 8 (1953), 1-79.
- [Haa87] U. Haagerup, A new upper bound for the complex Grothendieck constant,
  Israel J. Math. 60 (1987), 199–224.
- [HJM26] Sharper Bounds for the Complex Grothendieck Constant, arXiv:2609.25462 [math.FA].
- [Pis12] G. Pisier, Grothendieck’s theorem, past and present,
  Bull. Amer. Math. Soc. 49 (2012), 237-323.
-/

@[expose] public section

namespace ComplexGrothendieckConstant

open Complex Matrix
open scoped InnerProductSpace

/--
The matrix property that appears in the complex Grothendieck inequality.

Let `m ∈ ℕ` and `A` be a complex `m × m` matrix. Then it has the matrix property iff for all
complex numbers `s 1,...,s m` and `t 1,...,t m` satisfying `|s i|, |t j|≤ 1` it holds
`|∑ (A i j) * (s i) * (t j)| ≤ 1`.
-/
def HasMatrixProperty {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ s t : Fin m → ℂ,
    ((∀ i, ‖s i‖ ≤ 1) ∧ (∀ j, ‖t j‖ ≤ 1)) →
      ‖∑ i, ∑ j, A i j * s i * t j‖ ≤ 1

/--
Example: the zero matrix satisfies the matrix property.
-/
@[category test, AMS 42]
example {m : ℕ} : HasMatrixProperty (0 : Matrix (Fin m) (Fin m) ℂ) := by
  intro s t ⟨hs, ht⟩
  calc
    ‖∑ i, ∑ j, (0 : Matrix (Fin m) (Fin m) ℂ) i j * s i * t j‖
      = 0 := by simp
    _ ≤ 1 := zero_le_one

/--
Example: the identity matrix does not satisfy the matrix property for dimension `m ≥ 2`.
-/
@[category test, AMS 42]
example {m : ℕ} (hm : m ≥ 2) : ¬HasMatrixProperty (1 : Matrix (Fin m) (Fin m) ℂ) := by
  let s : Fin m → ℂ := fun i => 1
  have hs : ∀ i, ‖s i‖ ≤ 1 := by
    unfold s
    norm_num
  intro h
  specialize h s s ⟨hs, hs⟩
  have : (2 : ℝ) ≤ (1 : ℝ) := by calc
    (2 : ℝ) ≤ (m : ℝ) := by norm_cast -- hm
    _ = ‖∑ i, ∑ j, (1 : Matrix (Fin m) (Fin m) ℂ) i j * s i * s j‖ := by unfold s; simp [one_apply]
    _ ≤ (1 : ℝ) := h
  exact absurd this (by norm_num)

/--
The statement that `K` satisfies the complex Grothendieck inequality in every dimension.
-/
def IsUniversalConstant (K : ℝ) : Prop :=
  ∀ m n : ℕ, ∀ A : Matrix (Fin m) (Fin m) ℂ, HasMatrixProperty A →
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
The statement that `KGC`is exactly the complex Grothendieck Constant. There exists a unique such
constant, since the supremum is bounded by the constant established in `exists_universal_constant`.
-/
def IsKGC (KGC : ℝ) : Prop :=
  IsUniversalConstant KGC ∧ ∀ K, IsUniversalConstant K → KGC ≤ K

/--
Haagerups "sensible candidate" conjectured as complex Grothendieck Constant in [Haa87], defined as
`1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`
-/
noncomputable def haagerup_candidate.answer : ℝ :=
  (∫ θ in (0:ℝ)..(Real.pi / 2),
    Real.cos θ ^ 2 / √(1 + Real.sin θ ^ 2))⁻¹

/--
The conjecture that the complex Grothendieck Constant equals `1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`.

This was proposed as "sensible candidate" by Haagerup in [Haa87].
-/
@[category research open, question value, AMS 42 46 47]
theorem haagerup_candidate : IsKGC haagerup_candidate.answer := by
  sorry

end ComplexGrothendieckConstant
