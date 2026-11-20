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
# Tao's Optimization Constant 10b / Complex Grothendieck Constant

*Reference:* [Tao's optimization constant 10b](https://teorth.github.io/optimizationproblems/constants/10b.html)

Let `m ∈ ℕ` and `A` be a complex `m × m` matrix such that for all complex numbers `s 1,...,s m`
and `t 1,...,t m` satisfying `|s i|, |t j|≤ 1` it holds `|∑ (A i j) * (s i) * (t j)| ≤ 1`.
Let `n ∈ ℕ` and `x 1,...,x m` and `y 1,...,y m` be complex vectors in `ℂ ^ n` with
`‖x i‖, ‖y j‖ ≤ 1`. The complex Grothendieck constant `C10b` is the smallest number independent
of `n` and `m` for which  `|∑ (A i j) * ⟪x i, y j⟫_ℂ| ≤ C10b` for every such matrix `A` and all
such vectors `x i, y j`.

In [Haa87] Haagerup doubted that his upper bound is the exact value of `C10b`
and proposed the smaller candidate `1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`

Recent progress [HJM26] showed `1.4 < C10b < 1.404898554746`. Haagerup's candidate lies in between
these bounds.

*Remarks:* Shifting to 0 indexing in this formalization to follow lean conventions.
By zero padding, the square matrix formulation used in this file immediately generalizes to a
rectangular matrix formulation.
[Tao's optimization constant 10b] asks for `m` and `n` to be positive integers.
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

namespace Constant10b

open Complex Matrix
open scoped InnerProductSpace

/--
The matrix property that appears in the complex Grothendieck inequality.

Let `m ∈ ℕ` and `A` be a complex `m × m` matrix. Then it has the matrix property iff for all
complex numbers `s 1,...,s m` and `t 1,...,t m` satisfying `|s i|, |t j|≤ 1` it holds
`|∑ (A i j) * (s i) * (t j)| ≤ 1`.
-/
def hasMatrixProperty {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ s t : Fin m → ℂ,
    ((∀ i, ‖s i‖ ≤ 1) ∧ (∀ j, ‖t j‖ ≤ 1)) →
      ‖∑ i, ∑ j, A i j * s i * t j‖ ≤ 1

/--
The zero matrix satisfies `hasMatrixProperty`.
-/
@[category test, AMS 42]
lemma zero_has_matrix_property {m : ℕ} : hasMatrixProperty (0 : Matrix (Fin m) (Fin m) ℂ) := by
  intro s t ⟨hs, ht⟩
  calc
    ‖∑ i, ∑ j, (0 : Matrix (Fin m) (Fin m) ℂ) i j * s i * t j‖
      = 0 := by simp
    _ ≤ 1 := zero_le_one

/--
Example: the identity matrix does not satisfy `hasMatrixProperty` for dimension `m ≥ 2`.
-/
@[category test, AMS 42]
example {m : ℕ} (hm : m ≥ 2) : ¬hasMatrixProperty (1 : Matrix (Fin m) (Fin m) ℂ) := by
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
The set of all values `‖∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℂ‖` for arbitrary dimensions, complex `m × m`
matrices `A` with `hasMatrixProperty A` and complex vectors `x 1,...,x m` and `y 1,...,y m` in
`ℂ ^ n` with `‖x i‖, ‖y j‖ ≤ 1`.

The complex Grothendieck constant `C10b` is the supremum of this set.
-/
def grothendieckSet : Set ℝ :=
  {value | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
      (x y : Fin m → EuclideanSpace ℂ (Fin n)),
    hasMatrixProperty A ∧ (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧
    value = ‖∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℂ‖}

/--
The set `grothendieckSet` is nonempty.
-/
@[category test, AMS 42]
lemma grothendieck_set_nonempty : grothendieckSet.Nonempty :=
  ⟨0, 0, 0, 0, 0, 0, zero_has_matrix_property, by simp, by simp, by simp⟩

/--
There exists a finite bound in the Grothendieck inequality that is universal in dimension.
This can be quickly deduced from the real bound established in [Gro53], see [Pis12].
-/
@[category research solved, AMS 42 46 47]
theorem grothendieck_set_bounded : BddAbove grothendieckSet := by
  sorry

/--
The complex Grothendieck Constant. There exists a unique such
constant, since the supremum is bounded as established in `grothendieck_set_bounded`.
-/
@[optimization_constant "10b"]
noncomputable def C10b : ℝ := sSup grothendieckSet

/-- A lower bound, proven by Steven Heilman, Chris Jones, Giulio Malavolta in [HJM26]. -/
@[category research solved, AMS 42 46 47]
theorem c10b_lower_bound : 1.4 < C10b := by
  sorry

/-- An upper bound, proven by Steven Heilman, Chris Jones, Giulio Malavolta in [HJM26]. -/
@[category research solved, AMS 42 46 47]
theorem c10b_upper_bound : C10b < 1.404898554746 := by
  sorry

def mem_Ico_c10b.answer : ℝ := sorry

/-- How can the upper bound `1.404898554746` of [HJM26] be improved? -/
@[category research open, question value, AMS 42 46 47]
theorem mem_Ico_c10b : mem_Ico_c10b.answer ∈ Set.Ico C10b 1.404898554746 := by
  sorry

def mem_Ioc_c10b.answer : ℝ := sorry

/-- How can the lower bound $1.4$ of [HJM26] be improved? -/
@[category research open, question value, AMS 42 46 47]
theorem mem_Ioc_c10b : mem_Ioc_c10b.answer ∈ Set.Ioc 1.4 C10b := by
  sorry

def c10b_eq.answer : ℝ := sorry

/-- What is the exact value of the complex Grothendieck constant? -/
@[category research open, question value, AMS 42 46 47]
theorem c10b_eq : C10b = c10b_eq.answer := by
  sorry

/--
Haagerups "sensible candidate" conjectured as complex Grothendieck Constant in [Haa87], defined as
`1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`
-/
noncomputable def c10b_eq_haagerup.answer : ℝ :=
  (∫ θ in (0:ℝ)..(Real.pi / 2),
    Real.cos θ ^ 2 / √(1 + Real.sin θ ^ 2))⁻¹

/--
The conjecture that the complex Grothendieck Constant equals `1/(∫_0^(π/2) (cos^2 θ)/√(1+sin^2 θ) dθ) ≈ 1.40458`.

This was proposed as "sensible candidate" by Haagerup in [Haa87].
-/
@[category research open, question value, AMS 42 46 47]
theorem c10b_eq_haagerup : C10b = c10b_eq_haagerup.answer := by
  sorry

end Constant10b
