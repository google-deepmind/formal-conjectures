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
# De Giorgi's conjecture

This file states a conjecture of De Giorgi about entire solutions to $Δ u + u - u^3 = 0$.
The conjecture is a rigidity theorem: in spatial dimension $n ≤ 8$, the level sets of bounded solutions
which satisfy $∂₁u > 0$ everywhere are hyperplanes. It has been shown that the condition $n ≤ 8$ is sharp.

The main theorems are:
- `DeGiorgi_le_eight`: the conjecture holds in dimension $n ≤ 8$.
- `DeGiorgi_ge_nine`: the conclusion of the conjecture does not hold if $n ≥ 9$.

The cases $1 ≤ n ≤ 8$ are also listed individually to enable partial solutions.
The cases $1 ≤ n ≤ 3$ are solved, while $4 ≤ n ≤ 8$ remains open.

## Existing results
- The case $n = 1$ trivially holds ($u$ is injective since $∂_1 u > 0$).
- The case $n = 2$ was proven by Ghoussoub and Gui.
- The case $n = 3$ was proven by Ambrosio and Cabré.
- The case $4 ≤ n ≤ 8$ was proven under an extra assumption by Savin.
- The counterexample for $n ≥ 9$ was proven by Del Pino, Kowalczyk, and Wei.

## References
* [Ghoussoub, Gui](https://doi.org/10.1007/s002080050196),
  Mathematische Annalen 311 (1998) proves the conjecture for $n = 2$.
* [Ambrosio, Cabré](https://doi.org/10.1090/S0894-0347-00-00345-3),
  Journal of the American Mathematical Society 13 (2000) proves the conjecture for $n = 3$.
* [Savin](https://doi.org/10.4007/annals.2009.169.41),
  Annals of Mathematics 169 (2009) proves the case $4 ≤ n ≤ 8$ under an additional assumption.
* [Del Pino, Kowalczyk, Wei](http://dx.doi.org/10.4007/annals.2011.174.3.3),
  Annals of Mathematics 174 (2011) shows that the condition $n ≤ 8$ is sharp.
-/

open ContDiff Set InnerProductSpace MeasureTheory EuclideanGeometry
open scoped Laplacian

namespace DeGiorgi

variable {n : ℕ} [NeZero n]

/--
The function $u : ℝ^n → ℝ$ is a bounded classical solution to $Δ u + u - u^3 = 0$.
-/
structure IsBoundedSolution (u : ℝ^n → ℝ) : Prop where
  regular : ContDiff ℝ 2 u
  bounded : ∃ C, ∀ x, |u x| ≤ C
  solution : ∀ x, (Δ u x) + u x - (u x) ^ 3 = 0

/--
The first partial derivative of $u : ℝ^n → ℝ$ is strictly positive.
-/
def HasPositiveDeriv (u : ℝ^n → ℝ) : Prop :=
  ∀ x, 0 < lineDeriv ℝ u x (EuclideanSpace.single 0 1)

/--
The level sets of $u : ℝ^n → ℝ$ are hyperplanes. This is expressed by stating that there exists
some affine subspace with rank $n - 1$ which coincides with the level set.
-/
def HasHyperplaneLevelSets (u : ℝ^n → ℝ) : Prop :=
  ∀ y ∈ range u, ∃ S : AffineSubspace ℝ (ℝ^n),
    u⁻¹' {y} = S ∧ Module.finrank ℝ S.direction = n - 1

/--
The conclusion to De Giorgi's conjecture: if $u : ℝ^n → ℝ$ is a bounded classical solution to
$Δ u + u - u^3 = 0$ satisfying $∂₁u > 0$ everywhere, then the level sets of $u$ are hyperplanes.
-/
def DeGiorgi_conclusion (n : ℕ) [NeZero n] : Prop :=
  ∀ u : ℝ^n → ℝ, (IsBoundedSolution u ∧ HasPositiveDeriv u) → HasHyperplaneLevelSets u

/--
De Giorgi's conjecture holds in dimension $n ≤ 8$.
-/
@[category research open, AMS 35]
theorem DeGiorgi_le_eight (hn : n ≤ 8) : (DeGiorgi_conclusion n) := by
  sorry

/--
In dimension $n ≥ 9$, the conclusion of De Giorgi's conjecture does not hold.
-/
@[category research solved, AMS 35]
theorem DeGiorgi_ge_nine (hn : n ≥ 9) : ¬(DeGiorgi_conclusion n) := by
  sorry

/--
De Giorgi's conjecture trivially holds in dimension $n = 1$.
-/
@[category research solved, AMS 35]
theorem DeGiorgi_one : (DeGiorgi_conclusion 1) := by
  intro u ⟨hu_sol, hu_deriv⟩ y hy
  obtain ⟨x, rfl⟩ := Set.mem_range.mp hy
  refine ⟨affineSpan ℝ {x}, ?_, ?_⟩
  · rw [AffineSubspace.coe_affineSpan_singleton, ← image_singleton]
    apply preimage_image_eq
    refine .of_comp_right (g := fun t ↦ EuclideanSpace.single 0 t) ?_ ?_
    · refine (strictMono_of_deriv_pos fun t ↦ ?_).injective
      specialize hu_deriv <| EuclideanSpace.single 0 t
      rw [(by simp : t = t + 0), ← deriv_comp_const_add, Function.comp_def]
      unfold lineDeriv at hu_deriv
      convert hu_deriv
      aesop
    · exact fun t ↦ ⟨t 0, by ext; simp; grind⟩
  · simp [direction_affineSpan]

/--
De Giorgi's conjecture holds in dimension $n = 2$.
-/
@[category research solved, AMS 35]
theorem DeGiorgi_two : (DeGiorgi_conclusion 2) := by
  sorry

/--
De Giorgi's conjecture holds in dimension $n = 3$.
-/
@[category research solved, AMS 35]
theorem DeGiorgi_three : (DeGiorgi_conclusion 3) := by
  sorry

/--
De Giorgi's conjecture holds in dimension $n = 4$.
-/
@[category research open, AMS 35]
theorem DeGiorgi_four : (DeGiorgi_conclusion 4) := by
  sorry

/--
De Giorgi's conjecture holds in dimension $n = 5$.
-/
@[category research open, AMS 35]
theorem DeGiorgi_five : (DeGiorgi_conclusion 5) := by
  sorry

/--
De Giorgi's conjecture holds in dimension $n = 6$.
-/
@[category research open, AMS 35]
theorem DeGiorgi_six : (DeGiorgi_conclusion 6) := by
  sorry

/--
De Giorgi's conjecture holds in dimension $n = 7$.
-/
@[category research open, AMS 35]
theorem DeGiorgi_seven : (DeGiorgi_conclusion 7) := by
  sorry

/--
De Giorgi's conjecture holds in dimension $n = 8$.
-/
@[category research open, AMS 35]
theorem DeGiorgi_eight : (DeGiorgi_conclusion 8) := by
  sorry

end DeGiorgi
