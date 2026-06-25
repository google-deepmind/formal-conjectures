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

This file formalizes a conjecture of De Giorgi about entire solutions to $Δ u + u - u^3 = 0$.
The conjecture is a rigidity statement: in spatial dimension $n ≤ 8$, the level sets of bounded solutions
which satisfy $∂₁u > 0$ everywhere are hyperplanes. The condition $n ≤ 8$ is sharp.

The main theorems are:
- `DeGiorgi_le_eight`: the conjecture holds in dimension $n ≤ 8$.
- `DeGiorgi_ge_nine`: the conclusion of the conjecture does not hold if $n ≥ 9$.

## Existing results
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
The function $u : ℝⁿ → ℝ$ is a bounded classical solution to $Δ u + u - u^3 = 0$
-/
structure IsBoundedSolution
    (u : ℝ^n → ℝ) : Prop where
  regular : ContDiff ℝ 2 u
  bounded : ∃ C, ∀ x, |u x| ≤ C
  solution : ∀ x, (Δ u x) + u x - (u x) ^ 3 = 0

/--
The first partial derivative of $u : ℝⁿ → ℝ$ is strictly positive.
-/
def HasPositiveDeriv (u : ℝ^n → ℝ) : Prop :=
  ∀ x, lineDeriv ℝ u x (EuclideanSpace.single 0 1) > 0

/--
The level sets of $u : ℝⁿ → ℝ$ are hyperplanes. This is expressed by stating that the
rank of the affine span of the level set (viewed as a submodule of ℝ^n) is n - 1.
-/
def HasHyperplaneLevelSets (u : ℝ^n → ℝ) : Prop :=
  ∀ y, Module.finrank ℝ (affineSpan ℝ (u⁻¹' {y})).direction = (n - 1)

/--
The conclusion to De Giorgi's conjecture: if $u : ℝⁿ → ℝ$ is a bounded classical solution to
$Δ u + u - u^3 = 0$ satisfying $∂₁u > 0$ everywhere, then the level sets of $u$ are hyperplanes.
-/
def DeGiorgi_conclusion (n : ℕ) [NeZero n] : Prop :=
  ∀ u : ℝ^n → ℝ, IsBoundedSolution u → HasPositiveDeriv u → HasHyperplaneLevelSets u

/--
De Giorgi's conjecture holds in dimension n ≤ 8.
-/
@[category research open, AMS 35]
theorem DeGiorgi_le_eight (hn : n ≤ 8) : (DeGiorgi_conclusion n) := sorry

/--
In dimension $n ≥ 9$, the conclusion of De Giorgi's conjecture does not hold.
-/
@[category research solved, AMS 35]
theorem DeGiorgi_ge_nine (hn : n ≥ 9) : ¬(DeGiorgi_conclusion n) := sorry

end DeGiorgi
